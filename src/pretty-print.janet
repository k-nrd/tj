(defn pp-type [typ]
  (defn- pp-function [typ]
    (let [params (typ :params)
          ret (typ :ret)]
      (string 
        "Function "
        (unless (nil? params)
          (let [positional (params :positional)
                optional (params :optional)
                variadic (params :variadic)]
            (string 
              (unless (nil? positional)
                (string/format "%p " (map pp-type positional))
                "")
              (unless (nil? optional)
                (string/format "&opt %p " (map pp-type optional))
                "")
              (unless (nil? variadic)
                (string/format "& %p" (pp-type variadic))
                "")))
          "")
        (unless (nil? ret)
          (string/format "-> %p" (pp-type ret))
          ""))))
          
  (defn- pp-t [typ]
    (case (typ :name)
      :string "String"
      :buffer "Buffer"
      :number "Number"
      :nil "Nil"
      :symbol "Symbol"
      :boolean "Boolean"
      :keyword "Keyword"
      :fiber "Fiber"
      :any "Any"
      :function (pp-function typ)))
  
  (pp-t typ))
