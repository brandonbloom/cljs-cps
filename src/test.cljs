(ns cps.test
  (:use [cps :only (top-level-k)])
  (:require-macros [cps :refer (call-cc with-cc spawn)]))

(assert (= "A"
           (with-out-str
             (spawn
               (print \A)
               (call-cc identity)
               (print \B)))))

(assert (= "AB"
           (with-out-str
             (spawn
               (print \A)
               (with-cc k (k))
               (print \B)))))

(assert (= "ABC"
           (with-out-str
             (spawn
               (print \A)
               (print (str (with-cc k (k \B))))
               (print \C)))))

;(def a-k (atom nil))
;
;(do
;  (println "before")
;  (with-cc k (reset! a-k k))
;  (println "after"))
;
;(a-k)
;(a-k)
