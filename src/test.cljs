(ns cps.test
  (:require [cps :refer (Continuation continuation?)])
  (:require-macros [cps :refer (return raise call-cc with-cc spawn)]))

(spawn (call-cc #(assert (continuation? %))))

;#_(assert (= "A"
;           (with-out-str
;             (spawn
;               (print \A)
;               (cps/call-cc identity)
;               (print \B)));))

#_(assert (= "ABC"
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
