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

(define-funs-rec
    (
      (P ((IProveParameter0 Nat)) Bool)
      (IProveWellDefined_P ((IProveParameter0 Nat)) Bool)
      (P__0 ((IProveParameter0 Nat)) (IProvePFResult Bool))
      (P__1 ((IProveParameter0 Nat)) (IProvePFResult Bool))
      (P__2 ((IProveParameter0 Nat)) (IProvePFResult Bool))) 
    (
      (IProveResult (P__0 IProveParameter0))
      (IProveWellDefined (P__0 IProveParameter0))
      (if (is-Zero IProveParameter0) 
          (IProveMkResult true true)
          (P__1 IProveParameter0))
      (if (is-Succ IProveParameter0)
          (let ((IProveParameter1 (fst_Succ IProveParameter0)))
               (let ((i IProveParameter1)) 
                    (IProveMkResult (IProveWellDefined_P i) (P i))
           )) 
           (P__2 IProveParameter0)
      )
      (IProveMkResult false IProveUnderdeterminedBool)
   )
)


(declare-datatypes (T) ( (Maybe (Just (get T)) Nothing) ))
(declare-datatypes ((IProveList 1)) ((par (T) (nil (IProveInsert (head T) (tail (IProveList T)))))))



(declare-datatypes (T) ( (Maybe (Just (get T)) Nothing) ))
(declare-datatypes ((IProveList 1)) ((par (T) (nil (IProveInsert (head T) (tail (IProveList T)))))))

(declare-datatypes (T) ((FunctionStatus (Success (get T)) (Failure (recover T)))))
(declare-fun IProveUnderDetermined_f (Int)  Int)
(declare-fun IProveUnderDetermined_P (Int)  Bool)
(define-funs-rec
    (
      (f ((IProveParameter0 Int)) Int)
      (f__0 ((IProveParameter0 Int)) (FunctionStatus Int))
      (f__1 ((IProveParameter0 Int)) (FunctionStatus Int))
      (IProveWellDefined_f ((IProveParameter0 Int)) Bool)
      
      (P ((IProveParameter0 Int)) Bool)
      (P__0 ((IProveParameter0 Int)) (FunctionStatus Bool))
      (P__1 ((IProveParameter0 Int)) (FunctionStatus Bool))
      (IProveWellDefined_P ((IProveParameter0 Int)) Bool)
   ) 
   (
      (get (f__0 IProveParameter0))
      (let ((x IProveParameter0)) (if (> x 10) (Success 10) (if (> x 0) (Success 0) (f__1 IProveParameter0))))
      (Failure (IProveUnderDetermined_f IProveParameter0)) (is-Success (f__0 IProveParameter0))
      
      (get (P__0 IProveParameter0))
      (let ((_ IProveParameter0)) (Success true))
      (Failure (IProveUnderDetermined_P IProveParameter0))
      (is-Success (P__0 IProveParameter0))
   )
)







(assert (not (and (forall ((x Int)) (implies (> x 0) (P (f x)))) (forall ((x Int)) (implies (> x 0) (IProveWellDefined_f (f x)))))))

(check-sat)

(implies 
   (and 
      (or (P Zero) (not (P Zero)))
      (forall ((x Nat)) 
         (implies 
            (or (P x) (not (P x)))
            (or (P (Succ x)) (not (P (Succ x)))
         ))
      )
   )
   (forall ((x Nat)) (
      or (P x) (not (P x))
   ))
)
   