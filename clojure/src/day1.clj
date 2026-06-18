(ns day1
  (:require [clojure.string :as str]
            [clojure.java.io :as io]
            [clojure.set :as set] :verbose :reload-all
            ))

(def input (slurp "../input/1"))

(def pairs (into []
                 (comp
                  (map rest)
                  (map #(map parse-long %)))
                 (re-seq #"(\d+)\s+(\d+)" input)))

(println "yoyoyoyo")
(ns bloop)
(def bloopity day1/pairs)
(def z 123456)
(defn abcdefg [x y] (fn [t] (str x "hijklmn" y z t)))
(println "bloopin")
