(declare-const IProveUnderspecifiedInt IProveUnderspecifiedInt)

(define-fun-rec ListExchange ((ls (List Int)) (cs (List Int))) (List Int)
   (if ((_ is nil) ls)
      cs
      (ListExchange (tail ls) (insert (head ls) cs))
   )
)

(define-fun-rec ListReverse ((ls (List Int))) (List Int) (ListExchange ls nil))
(define-fun-rec ListConcat ((ls (List Int)) (cs (List Int))) (List Int) 
   (ListExchange (ListReverse ls) cs))

(define-fun-rec ListElem ((ls (List Int)) (i Int)) Int
   (if ((_ is nil) ls)
      IProveUnderspecifiedInt
      (if (= i 0)
         (head ls)
         (ListElem (tail ls) (- i 1))
      )
   )
)

(define-fun-rec ListSlice ((ls (List Int)) (s Int) (e Int) (cs (List Int))) (List Int)
   (if ((_ is nil) ls)
      (ListReverse cs)
      (if (= e 0)
         (ListReverse cs)
         (if (= s 0)
            (ListSlice (tail ls) 0 (- e 1) (insert (head ls) cs))
            (ListSlice (tail ls) (- s 1) (- e 1) cs)
         )
      )
   )
)