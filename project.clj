(defproject cljs-cps "0.0.1"
  :plugins [[lein-cljsbuild "0.2.9"]]
  :source-paths ["src"
                 "clojurescript/src/clj"
                 "clojurescript/src/cljs"]
  :cljsbuild {
    :builds [{
        :source-path "src"
        :compiler {
          :output-to "out/main.js"
          :optimizations :whitespace
          :pretty-print true}}]})
