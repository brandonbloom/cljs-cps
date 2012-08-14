(ns anf
  (:require [cljs.compiler :as comp]
            [cljs.analyzer :as ana]))

(defn analyze [form]
  (let [env (ana/empty-env)] ;TODO: How to get the "current" environment?
    (ana/analyze env form)))

;;TODO: Namespace these ops
(def control-ops #{'shift 'reset}) ; Alternatively, call-cc & friends.

;;TODO: Possible optimization: annontation pass, this becomes O(1)
;; Downside: Must manually re-run annotation pass when re-creating forms.
;; Could potentially bypass downside with pluggable hooks in base analyze.
(defn trivial?
  "Trivial expressions definitely do not evaluate any control forms."
  [{:keys [op children] :as ast}]
  (cond
    (= op :var) (not (-> ast :info :cps))
    :else (every? trivial? children)))

(defn serious?
  "Serious expressions might evaluate one or more control forms."
  [ast]
  (not (trivial? ast)))

(defmulti anf
  "Applies an Administrative Normal Form transformation to an AST.
  The transformation is selective with regard to trivial expressions."
  :op)

(defn anf*
  "Applies a selective ANF transform to a form."
  [form]
  (-> (analyze form) anf :form))

(defmethod anf :default
  [{:keys [env op] :as ast}]
  (when-not (#{:var} op)
    (ana/warning env (str "Unsupported op " op " in ANF transform")))
  ast)

(defmethod anf :invoke
  [{:keys [env children] :as ast}]
  (if (trivial? ast)
    ast
    (let [syms (repeatedly (count children) #(gensym "anf"))
          forms (map :form children)]
      (ana/analyze env `(let [~@(interleave syms forms)]
                          (~@syms))))))

;;TODO ALL THE OPS!
;(defmethod cps :meta
;(defmethod cps :map
;(defmethod cps :vector
;(defmethod cps :set
;(defmethod cps :constant
;(defmethod cps :if
;(defmethod cps :throw
;(defmethod cps :def
;(defmethod cps :fn
;(defmethod cps :do
;(defmethod cps :try*
;(defmethod cps :let
;(defmethod cps :recur
;(defmethod cps :new
;(defmethod cps :set!
;(defmethod cps :ns
;(defmethod cps :deftype*
;(defmethod cps :defrecord*
;(defmethod cps :dot
;(defmethod cps :js

(defmulti cps
  "Applies a Continuation Passing Style transformation to an AST.
  The transformation is selective with regard to trivial expressions and
  assumes that serious call-sites are in Administrative Normal Form."
  :op)

(defn cps*
  "Applies a selective CPS transform to a form."
  [form]
  (-> (analyze form) anf cps :form))

(defmethod cps :default
  [{:keys [env op] :as ast}]
  ;;TODO: Error? Generic walk? Something else? See also anf :default
  (ana/warning env (str "Unsupported op " op " in CPS transform"))
  ast)

(defmethod cps :invoke
  [{:keys [env f args] :as ast}]
  ast)

;;TODO ALL THE OPS!
;(defmethod cps :invoke
;(defmethod cps :var
;(defmethod cps :meta
;(defmethod cps :map
;(defmethod cps :vector
;(defmethod cps :set
;(defmethod cps :constant
;(defmethod cps :if
;(defmethod cps :throw
;(defmethod cps :def
;(defmethod cps :fn
;(defmethod cps :do
;(defmethod cps :try*
;(defmethod cps :let
;(defmethod cps :recur
;(defmethod cps :new
;(defmethod cps :set!
;(defmethod cps :ns
;(defmethod cps :deftype*
;(defmethod cps :defrecord*
;(defmethod cps :dot
;(defmethod cps :js

(comment

(use '[clojure.pprint :only (pprint)])

(pprint (anf* 'x))

;; Toggle back and forth between these to test re-defining-away the metadata.
;; Metadata was bugged on redef in the CLJS compiler and I have a fix.
(trivial? (analyze '(do (defn f [x] x) (f 1))))
(trivial? (analyze '(do (defn ^:cps f [x] x) (f 1))))

(pprint (anf* '(f x)))

(analyze '(defn ^:cps cps-inc [x] (inc x)))

(pprint (anf* '(cps-inc x)))

)
