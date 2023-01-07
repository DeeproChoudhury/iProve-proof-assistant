(declare-const IProveUnderspecified${t} ${t})

(define-fun-rec ListExchange ((ls (List ${t})) (cs (List ${t}))) (List ${t})
   (if ((_ is nil) ls)
      cs
      (ListExchange (tail ls) (insert (head ls) cs))
   )
)

(define-fun-rec ListReverse ((ls (List ${t}))) (List ${t}) (ListExchange ls nil))
(define-fun-rec ListConcat ((ls (List ${t})) (cs (List ${t}))) (List ${t}) 
   (ListExchange (ListReverse ls) cs))

(define-fun-rec ListElem ((ls (List ${t})) (i ${t})) ${t}
   (if ((_ is nil) ls)
      IProveUnderspecified${t}
      (if (= i 0)
         (head ls)
         (ListElem (tail ls) (- i 1))
      )
   )
)

(define-fun-rec ListSlice ((ls (List ${t})) (s ${t}) (e ${t}) (cs (List ${t}))) (List ${t})
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