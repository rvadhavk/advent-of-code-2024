(ns blah
  (:require [clojure.core.match :refer [match]]))

(ndefn position-x [root x-min]
  (match [(root :left) (root :right)]
         [nil nil] [(assoc root :x x-min) x-min]
         [nil r] (let [[r' x-max] (position-x r x-min)]
                   [(merge root {:x (r' :x) :right r'}) x-max])
         [l nil] (let [[l' x-max] (position-x l x-min)]
                   [(merge root {:x (l' :x) :left l'}) x-max])
         [l r] (let [(l' l-x-max) (position-x l x-min)
                     (r' r-x-max) (position-x r l-x-max)]
                 [(merge root {:x (avg (r' :x) (l' :x)) :left 'l :right 'r}) r-x-max])))
