(ns day3)

(def c 10)
(defn emp [] (+ c 55))
(defn bloop [& x] (apply / 2 x))
(defn foo [x]
  ;(println "hi")
  (bloop 8 9)
  (emp)
  (* x 3))

(defn bar [x]
  (str (+ (emp) (foo x))
       (emp)
       (bloop x)
       (bloop (foo x) (foo 4))))


