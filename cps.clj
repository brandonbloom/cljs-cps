(ns cps
  (:require [cljs.compiler :as comp]
            [cljs.analyzer :as ana]))

;; TODO: Put this into the env
;(def ^:dynamic *k* 'cps/top-level-k)

(defmacro call-cc [f & args]
  (throw (Exception. "call-cc must be used within a cps transform")))

(defmacro return [k value]
  (throw (Exception. "return must be used within a cps transform")))

(defmacro raise [k error]
  (throw (Exception. "raise must be used within a cps transform")))

(def control-ops `#{call-cc return raise})

(defn control-op?
  [{:keys [op info] :as ast}]
  (and (= op :var) (contains? control-ops (:name info))))

;;TODO: Possible optimization: annontation pass, this becomes O(1)
;; Downside: Must manually re-run annotation pass when re-creating forms.
;; Could potentially bypass downside with pluggable hooks in base analyze.
(defn serious?
  "Serious expressions might evaluate one or more control forms."
  [{:keys [op f children] :as ast}]
  (or (and (= op :invoke) (control-op? f))
      (boolean (some serious? children))))

(defn trivial?
  "Trivial expressions definitely do not evaluate any control forms."
  [ast]
  (not (serious? ast)))

;;TODO: Nearly all use of metadata in analyze causes data loss when transformed

(defmulti anf
  "Applies an Administrative Normal Form transformation to an AST.
  The transformation is selective with regard to trivial expressions."
  :op)

(def anf* (comp :form anf))

(defmethod anf :default
  [{:keys [env op] :as ast}]
  (when-not (#{:ns :var :constant :js :deftype* :defrecord*} op)
    (ana/warning env (str "Unsupported op " op " in ANF transform")))
  ast)

(defn- anf-application [{:keys [env] :as ast} key f]
  (let [args (key ast)]
    (if (every? trivial? args)
      ast
      (let [syms (repeatedly (count args) gensym)
            forms (map anf* args)]
        (ana/analyze env `(let [~@(interleave syms forms)]
                            ~(f syms)))))))

(defmethod anf :invoke
  [{:keys [f] :as ast}]
  (if (control-op? f)
    (anf-application ast :args #(cons (:form f) %)))
    (anf-application ast :children identity))

(defmethod anf :new
  [ast]
  (anf-application ast :children #(cons 'new %)))

(defmethod anf :throw
  [ast]
  (anf-application ast :children #(cons 'throw %)))

(defmethod anf :recur
  [ast]
  (anf-application ast :exprs #(cons 'recur %)))

(defmethod anf :map
  [ast]
  (anf-application ast :children #(apply hash-map %)))

(defmethod anf :vector
  [ast]
  (anf-application ast :items vec))

(defmethod anf :set
  [ast]
  (anf-application ast :items set))

(defmethod anf :set!
  [{:keys [env target val] :as ast}]
  (if (trivial? val)
    ast
    (ana/analyze env `(let [val# ~(anf* val)]
                        (set! ~(:form target) val#)))))

(defmethod anf :if
  [{:keys [env test then else] :as ast}]
  (let [then (anf* then)
        else (when else [(anf* else)])]
    (ana/analyze env (if (trivial? test)
                       `(if ~(:form test) ~then ~@else)
                       `(let [test# ~(anf* test)]
                          (if test# ~then ~@else))))))

;;TODO: Test this! Turns out that it's tricky to work around the reader.
(defmethod anf :meta
  [{:keys [env meta expr children] :as ast}]
  (if (every? trivial? children)
    ast
    ;NOTE: funky expr/meta evaluation order matches emit phase
    (ana/analyze env `(let [expr# ~(anf* expr)
                            meta# ~(anf* meta)]
                        (cljs.core/with-meta expr# meta#)))))

(defn- anf-block
  [{:keys [statements ret] :as ast}]
  (when ast
    (let [children (conj (vec statements) ret)]
      (map anf* children))))

(defmethod anf :do
  [{:keys [env children] :as ast}]
  (ana/analyze env `(do ~@(anf-block ast))))

(defmethod anf :try*
  [{:keys [env try catch name finally] :as ast}]
  (ana/analyze env `(~'try*
                     ~@(anf-block try)
                     ~@(when catch
                         (list (list* 'catch name
                                      (anf-block catch))))
                     ~@(when finally
                         (list (cons 'finally
                                     (anf-block finally)))))))

(defn- anf-bindings
  [{:keys [env bindings form] :as ast}]
  (ana/analyze env `(~(first form)
                        [~@(mapcat (fn [{:keys [name init]}]
                                     [name (anf* init)])
                                   bindings)]
                        ~@(anf-block ast))))

(defmethod anf :let
  [ast]
  (anf-bindings ast))

(defmethod anf :letfn
  [ast]
  (anf-bindings ast))

(defmethod anf :dot
  [{:keys [env target field method form] :as ast}]
  (if (serious? target)
    (anf (ana/analyze env `(let [target# ~(:form target)]
                             (~'. target# ~@(drop 2 form)))))
    (if field
      ast
      (anf-application ast :args #(concat (take 3 form) %)))))

(defmethod anf :def
  [{:keys [env init form] :as ast}]
  (if (trivial? init)
    ast
    (ana/analyze env `(let [init# ~(anf* init)]
                        (~@(butlast form) init#)))))

(defmethod anf :fn
  [{:keys [env form methods] :as ast}]
  (let [prefix (first (split-with (complement seq?) form))]
    (ana/analyze env `(~@prefix ~@(map (fn [{:keys [form] :as method}]
                                         `(~(first form) ~@(anf-block method)))
                                       methods)))))



;; CPS STUFF BELOW

(defn- wrap-return
  [{:keys [env context] :as ast} k]
  (if (and k (= context :return))
    (ana/analyze env `(k-return ~k)
    k)))

(defmulti cps
  "Applies a Continuation Passing Style transformation to an AST.
  The transformation is selective with regard to trivial expressions and
  assumes that serious expressions are in Administrative Normal Form."
  (fn [ast k]
    (:op ast)))

(defmethod cps :default
  [{:keys [env op] :as ast} k]
  ;;TODO: Error? Generic walk? Something else? See also anf :default
  (ana/warning env (str "Unsupported op " op " in CPS transform"))
  ast)

(defmethod cps :invoke
  [{:keys [env f args] :as ast} k]
  (if (trivial? ast)
    ast
    DO-STUFF-HERE))

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
;(defmethod cps :let           ; if loop, use trampoline-like thing
;(defmethod cps :letfn
;(defmethod cps :recur
;(defmethod cps :new
;(defmethod cps :set!
;(defmethod cps :ns
;(defmethod cps :deftype*
;(defmethod cps :defrecord*
;(defmethod cps :dot
;(defmethod cps :js

(comment

(defn analyze [form]
  (ana/analyze (ana/empty-env) form))

(use '[clojure.pprint :only (pprint)])

(defn dbg [x]
  (println "------------")
  (pprint x)
  (println "------------")
  x)

(trivial? (analyze '(defn f [x] x)))

(trivial? (analyze '(defn f [] (cps/call-cc identity))))

(defn show-anf [form]
  (-> form
    analyze
    anf
    :form
    pprint))

(show-anf 1)

(show-anf '(identity 1))

(show-anf '(identity 1 (cps/call-cc 2) 3 (cps/call-cc 4)))

(show-anf '(Integer. 1))

(show-anf '(Integer. (cps/call-cc 1)))

(show-anf '(set! x 1))

(show-anf '(set! x (cps/call-cc 1)))

(show-anf '(set! x (identity (cps/call-cc 1))))

(show-anf '(if 1 2))

(show-anf '(if 1 2 3))

(show-anf '(if (cps/call-cc 1) 2 3))

(show-anf '(if 1 (identity (cps/call-cc 2)) 3))

(show-anf '(if (cps/call-cc 1) (identity (cps/call-cc 2)) 3))

(show-anf '{:x 1})

(show-anf '{(cps/call-cc 1) 2})

(show-anf '[1])

(show-anf '[(cps/call-cc 1)])

(show-anf '#{1})

(show-anf '#{(cps/call-cc 1)})

(show-anf '(throw 1))

(show-anf '(throw (cps/call-cc 1)))

(show-anf '(do))

(show-anf '(do 1 2 3))

(show-anf '(do
             1
             (identity (cps/call-cc 2))
             3))

(show-anf '(let [x 1]
             (identity x)))

(show-anf '(let [x (identity (cps/call-cc 1))]
             2))

(show-anf '(let [x 1]
             (identity (cps/call-cc 2))))

(show-anf '(try 1))

(show-anf '(try (throw (cps/call-cc 1))))

(show-anf '(try 1 (catch Error e 2)))

(show-anf '(try 1 (finally 2)))

(show-anf '(try 1 (catch Error e 2) (finally 3)))

(show-anf '(try 1
             (catch Error e (identity (cps/call-cc 2)))
             (finally (identity (cps/call-cc 3)))))

(show-anf '(.f 1 2))

(show-anf '(.f (cps/call-cc 1) 2))

(show-anf '(.f 1 (cps/call-cc 2)))

(show-anf '(def x 1))

(show-anf '(def x (cps/call-cc 1)))

(show-anf '(fn [x] x))

(show-anf '(fn ([x] x) ([x y] x)))

(show-anf '(fn [x] (identity (cps/call-cc x))))

(show-anf '(fn ([x] (identity (cps/call-cc x)))
               ([x y] (identity (cps/call-cc x y)))))

(show-anf '(letfn [(f [x] x)] (f 1)))

(show-anf '(letfn [(f [x] (identity (cps/call-cc x)))] (f 1)))

(show-anf '(deftype T [x] P (f [x] x)))

(show-anf '(deftype T [x] P (f [x] (identity (cps/call-cc x)))))

(show-anf '(defrecord R [x] P (f [x] x)))

(show-anf '(defrecord R [x] P (f [x] (identity (cps/call-cc x)))))


;TODO? (trivial? (analyze '(do (defn ^:cps f [x] x) (f 1))))

)
