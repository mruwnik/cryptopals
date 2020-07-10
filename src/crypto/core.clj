(ns crypto.core
  (:gen-class)
  (:require [clojure.string :as str]
            [clojure.java.io :as io])
  (:import java.util.Base64
           [javax.crypto.spec SecretKeySpec]
           [javax.crypto Cipher KeyGenerator SecretKey]
           [java.security SecureRandom]))

(defn char->num [char]
  ({\0 0 \1 1 \2 2 \3 3 \4 4 \5 5 \6 6 \7 7 \8 8 \9 9 \a 10 \b 11 \c 12 \d 13 \e 14 \f 15} char))

(def base64-to-table
  {0 \A 1 \B 2 \C 3 \D 4 \E 5 \F 6 \G 7 \H 8 \I 9 \J 10 \K 11 \L 12 \M 13 \N
   14 \O 15 \P 16 \Q 17 \R 18 \S 19 \T 20 \U 21 \V 22 \W 23 \X 24 \Y 25 \Z 26 \a
   27 \b 28 \c 29 \d 30 \e 31 \f 32 \g 33 \h 34 \i 35 \j 36 \k 37 \l 38 \m 39 \n
   40 \o 41 \p 42 \q 43 \r 44 \s 45 \t 46 \u 47 \v 48 \w 49 \x 50 \y 51 \z
   52 \0 53 \1 54 \2 55 \3 56 \4 57 \5 58 \6 59 \7 60 \8 61 \9 62 \+ 63 \/})
(def base64-from-table (into {} (map (comp vec reverse) base64-to-table)))

(defn str->bytes [val] (map (comp byte int) val))
(defn format-hex [bytes] (apply str (map (partial format "%02x") bytes)))
(defn read-hex [bytes] (apply str (map char bytes)))
(defn str->hex [val]
  (->> (if (even? (mod (count val) 2)) val (str "0" val))
       str/lower-case
       (map char->num)
       (remove nil?)
       (partition 2)
       (map (fn [[a1 a0]] (+ (* 16 a1) a0)))))
(defn bytes->str [val] (->> val (map char) (apply str)))

(defn clj-encode [to-encode]
  (.encodeToString (Base64/getEncoder) (.getBytes to-encode)))

(defn clj-decode [to-decode]
  (String. (.decode (Base64/getDecoder) to-decode)))


(defn convert-triplet
  ([b1] (conj (vec (take 2 (convert-triplet b1 0 0))) \= \=))
  ([b1 b2] (conj (vec (take 3 (convert-triplet b1 b2 0))) \=))
  ([b1 b2 b3]
   (map base64-to-table
        [(bit-shift-right b1 2)
         (bit-or (bit-shift-left (bit-and 0x03 b1) 4) (bit-shift-right b2 4))
         (bit-or (bit-shift-left (bit-and 0x0F b2) 2) (bit-shift-right b3 6))
         (bit-and 0x3F b3)])))

(defn quad->triplet
  ([b1 b2] (take 1 (quad->triplet b1 b2 \A \A)))
  ([b1 b2 b3] (take 2 (quad->triplet b1 b2 b3 \A)))
  ([b1 b2 b3 b4]
   [(bit-or (bit-shift-left (base64-from-table b1) 2) (bit-shift-right (base64-from-table b2) 4))
    (bit-or (bit-and 0xF0 (bit-shift-left (base64-from-table b2) 4)) (bit-shift-right (base64-from-table  b3) 2))
    (bit-or (bit-and 0xFB (bit-shift-left (base64-from-table b3) 6)) (bit-and (base64-from-table b4) 0x3F))]))

(defn bytes->base64 [val]
  (->> val (partition 3 3 "") (map (partial apply convert-triplet)) flatten (apply str)))
(defn base64->bytes [text]
  (->> (str/replace text "=" "") (partition 4 4 "") (map (partial apply quad->triplet)) flatten))


(defn keyed-xor [val key] (map bit-xor val (cycle key)))
(defn file-xor [filename key]
  (-> filename slurp str->bytes (keyed-xor (str->bytes key))))

(defn ascii-text? [val]
  (every? #(or (and (> (int %) 31) (< (int %) 126)) (#{9 10 13} (int %))) val))
(defn commonality-score
  "Score the given text on how much of it consists of the most common letters."
  [text]
  (/ (->> text str/lower-case (filter #{\e \t \a \o \i \n \space \s \h \r \d \l \u}) count)
     (count text)))

(defn best-fixed-xors
  "Guess at the character that was most likely to xor the given cryptotext."
  [input]
    (->> (range 255)
         (map #(vector % (read-hex (keyed-xor input [%]))))
         (filter (comp ascii-text? second))
         (sort-by (comp commonality-score second))
         reverse))

(defn hamming-bits [a b] (count (filter (partial bit-test (bit-xor a b)) (range 8))))
(defn hamming-dist
  "The Hamming distance (bitwise) between two sets of bytes."
  [a b] (reduce + (map hamming-bits a b)))

(defn normalised-dist [text blocksize]
  (/ (->> text (partition (* blocksize 4)) (take 2) (apply hamming-dist))
     (* blocksize 4)))

(defn guess-key-size [cyphertext max-size]
  (->> (range 1 max-size) (map #(vector % (normalised-dist cyphertext %))) (sort-by second)))

(defn guess-vigenere-key [cyphertext keysize]
  (->> cyphertext
       (partition keysize)
       (apply map vector)
       (map best-fixed-xors)
       (map ffirst)
       bytes->str))


(defn get-raw-key [seed]
  (let [keygen (KeyGenerator/getInstance "AES")
        sr (SecureRandom/getInstance "SHA1PRNG")]
    (.setSeed sr (bytes seed))
    (.init keygen 128 sr)
    (.. keygen generateKey getEncoded)))

(defn get-cipher [mode seed]
  (let [key-spec (SecretKeySpec. (get-raw-key seed) "AES")
        cipher (Cipher/getInstance "AES")]
    (.init cipher mode key-spec)
    cipher))

(defn encrypt-aes [text key]
  (let [bytes (bytes text)
        cipher (get-cipher Cipher/ENCRYPT_MODE key)]
    (base64 (.doFinal cipher bytes))))

(defn decrypt-aes [cyphertext key]
  (let [cipher (get-cipher Cipher/DECRYPT_MODE (byte-array key))]
    (String. (.doFinal cipher (bytes (byte-array cyphertext))))))

(let [cyphertext (-> "data-1-7.txt" io/resource slurp (str/replace #"\n" "") base64->bytes)
      key "YELLOW SUBMARINE"]
  (decrypt-aes cyphertext key))
(def cyphertext (-> "data-1-7.txt" io/resource slurp (str/replace #"\n" "") base64->bytes))
(def cipher (get-cipher Cipher/DECRYPT_MODE (byte-array (str->bytes "YELLOW SUBMARINE"))))
(decrypt-aes cyphertext "YELLOW SUBMARINE")


                                        ; https://cryptopals.com/sets/1/challenges/7
(when nil
  ;; 1-3
  (best-fixed-xors (str->hex "1b37373331363f78151b7f2b783431333d78397828372d363c78373e783a393b3736"))

  ;; 1-4
  (->>
   (-> "data-1-4.txt" io/resource slurp (str/split #"\n"))
   (map str->hex )
   (map (comp first best-fixed-xors))
   (filter not-empty)
   (sort-by (comp commonality-score second))
   reverse)

  ;; 1-5

  (->
   (keyed-xor (str->bytes "Burning 'em, if you ain't quick and nimble I go crazy when I hear a cymbal")
              (str->bytes "ICE"))
   format-hex)

  ;; 1-6
  (let [cyphertext (-> "data-1-6.txt" io/resource slurp (str/replace #"\n" "") base64->bytes)
        key (guess-vigenere-key cyphertext (ffirst (guess-key-size cyphertext 40)))]
    (->>
     (str->bytes key)
     (keyed-xor cyphertext)
     bytes->str
     println))

  )

(-> (file-xor "/etc/passwd" "blabla") bytes->str println)

(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, World!"))
