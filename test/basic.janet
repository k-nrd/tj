(import ../src/main :as t)

(assert (= (t/type-check 10) t/num))
(assert (= (t/type-check "string") t/str))
