(ns day2
  (:require [clojure.set :as set]
            [clojure.string :as str]
            [clojure.math :refer [signum]]
            [clojure.test :refer [deftest is testing]]))

(def example-input
"7 6 4 2 1
1 2 7 8 9
9 7 6 2 1
1 3 2 4 5
8 6 4 4 1
1 3 6 7 9")

(defn parse [lines]
  "Parses a grid of integers where each element is separated by a space
   and each row separated by a newline into a vector of vectors"
  (letfn [(parse-line [l] (mapv parse-long (str/split l #"\s+")))]
    (mapv parse-line (str/split-lines lines))))

(deftest parse-example-test
  (is (= [[7 6 4 2 1]
          [1 2 7 8 9]
          [9 7 6 2 1]
          [1 3 2 4 5]
          [8 6 4 4 1]
          [1 3 6 7 9]]
         (parse example-input))))

(defn diffs [coll]
  (map - (next coll) coll))

(defn part1-safe? [report]
  (let [diffs (diffs report)]
    (and
     (apply = (map signum diffs))
     (every? #(<= 1 % 3) (map abs diffs)))))

(defn part1 [reports]
  (count (filter part1-safe? reports)))

(deftest part1-example-test
  (is (= 2 (part1 (parse example-input)))))

(defn part2-safe? [report]
  (some part2-safe-increasing? [report (reverse report)]))

(deftest part2-safe?-test
  (is (part2-safe? [7 6 4 2 1]))
  (is (not (part2-safe? [1 2 7 8 9])))
  (is (not (part2-safe? [9 7 6 2 1])))
  (is (part2-safe? [1 3 2 4 5]))
  (is (part2-safe? [8 6 4 4 1]))
  (is (part2-safe? [1 3 6 7 9])))
(defn part2 [reports]
  (count (filter part2-safe? reports)))

(deftest part2-example-test
  (is (= 4 (part2 (parse example-input)))))
