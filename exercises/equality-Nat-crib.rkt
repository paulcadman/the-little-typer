#lang pie

;; Exercises on Nat equality from Chapter 8 and 9 of The Little Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (_ b+a-k)
               (add1 b+a-k)))))

;; Exercise 8.1
;; Define a function called zero+n=n that states and proves that
;; 0+n = n for all Nat n.

(claim zero+n=n
       (Π ([n Nat])
          (= Nat (+ zero n) n)))

(define zero+n=n
  (λ (n)
    (same n)))

;; Exercise 8.2
;;
;; Define a function called a=b->a+n=b+n that states and proves that
;; a = b implies a+n = b+n for all Nats a, b, n.

(claim a=b->a+n=b+n
       (Π ([a Nat]
           [b Nat]
           [n Nat])
          (-> (= Nat a b)
              (= Nat (+ a n) (+ b n)))))

(define a=b->a+n=b+n
  (λ (a b n)
    (λ (a=b)
      (replace a=b
               (λ (k)
                 (= Nat (+ a n) (+ k n)))
               (same (+ a n))))))

;; Exercise 8.3
;;
;; Define a function called plusAssociative that states and proves that
;; + is associative.

(claim plusAssociative
       (Π ([n Nat]
           [m Nat]
           [k Nat])
          (= Nat (+ k (+ n m)) (+ (+ k n) m))))

(claim mot-plusAssociative
       (-> Nat Nat Nat
           U))

(define mot-plusAssociative
  (λ (m p n)
    (= Nat (+ n (+ m p)) (+ (+ n m) p))))

(claim base-plusAssociative
       (Π ([m Nat]
           [p Nat])
          (mot-plusAssociative m p zero)))

(define base-plusAssociative
  (λ (m p)
    (same (+ m p))))

(claim step-plusAssociative
       (Π ([m Nat]
           [p Nat]
           [n Nat])
          (-> (mot-plusAssociative m p n)
              (mot-plusAssociative m p (add1 n)))))

(define step-plusAssociative
  (λ (m p n)
    (λ (plusAssociative-n)
      (cong plusAssociative-n (+ 1)))))

(define plusAssociative
  (λ (m p n)
    (ind-Nat n
             (mot-plusAssociative m p)
             (base-plusAssociative m p)
             (step-plusAssociative m p))))


;; Exercise 9.1
;;
;; Define a function called same-cons that states and proves that
;; if you cons the same value to the front of two equal Lists then
;; the resulting Lists are also equal.

(claim same-cons
       (Π ([E U]
           [l1 (List E)]
           [l2 (List E)]
           [e E])
          (-> (= (List E) l1 l2)
              (= (List E) (:: e l1) (:: e l2)))))

(define same-cons
  (λ (E l1 l2 e)
    (λ (prf)
      (replace prf
               (λ (l)
                 (= (List E) (:: e l1) (:: e l)))
               (same (:: e l1))))))


;; Exercise 9.2
;;
;; Define a function called same-lists that states and proves that
;; if two values, e1 and e2, are equal and two lists, l1 and l2 are
;; equal then the two lists, (:: e1 l1) and (:: e2 l2) are also equal.

(claim same-lists
       (Π ([E U]
           [l1 (List E)]
           [l2 (List E)]
           [e1 E]
           [e2 E])
          (-> (= E e1 e2) (= (List E) l1 l2)
              (= (List E) (:: e1 l1) (:: e2 l2)))))

(define same-lists
  (λ (E l1 l2 e1 e2)
    (λ (e1=e2 l1=l2)
      (replace e1=e2
               (λ (k)
                 (= (List E) (:: e1 l1) (:: k l2)))
               (same-cons E l1 l2 e1 l1=l2)))))
#;(define same-lists
  (λ (E l1 l2 e1 e2)
    (λ (prf-e prf-l)
      (replace prf-e
               (λ (k)
                 (= (List E) (:: e1 l1) (:: k l2)))
               (same-cons E l1 l2 e1 prf-l)))))


;; Exercise 9.3 (was previously called Exercise 8.4)
;;
;; Define a function called plusCommutative that states and proves that
;; + is commutative
;;
;; Bonus: Write the solution using the trans elimiator instead of
;; the replace elimiator.
;; https://docs.racket-lang.org/pie/index.html#%28def._%28%28lib._pie%2Fmain..rkt%29._trans%29%29

(claim plusCommutative
       (Π ([n Nat]
           [m Nat])
          (= Nat (+ n m) (+ m n))))

(claim mot-plusCommutative
       (-> Nat Nat
           U))

(define mot-plusCommutative
  (λ (n m)
    (= Nat (+ n m) (+ m n))))

(claim base-plusCommutative
       (Π ([n Nat])
          (mot-plusCommutative n zero)))

(claim mot-base-plusCommutative
       (-> Nat
           U))

(define mot-base-plusCommutative
  (λ (n)
    (mot-plusCommutative n zero)))

(claim base-base-plusCommutative
       (= Nat zero zero))

(define base-base-plusCommutative
  (same zero))

(claim step-base-plusCommutative
       (Π ([n Nat])
          (-> (mot-base-plusCommutative n)
              (mot-base-plusCommutative (add1 n)))))

(define step-base-plusCommutative
  (λ (n)
    (λ (n+0=0+n)
      (cong n+0=0+n (+ 1)))))

(define base-plusCommutative
  (λ (n)
    (ind-Nat n
             mot-base-plusCommutative
             base-base-plusCommutative
             step-base-plusCommutative)))

(claim add1-right
       (Π ([n Nat]
           [m Nat])
          (= Nat
             (+ m (add1 n))
             (add1 (+ m n)))))

(claim mot-add1-right
       (-> Nat Nat
           U))

(define mot-add1-right
  (λ (n m)
    (= Nat
       (+ m (add1 n))
       (add1 (+ m n)))))

(claim base-add1-right
       (Π ([n Nat])
          (mot-add1-right n zero)))

(define base-add1-right
  (λ (n)
    (same (add1 n))))

(claim step-add1-right
       (Π ([n Nat]
           [m Nat])
          (-> (mot-add1-right n m)
              (mot-add1-right n (add1 m)))))

(define step-add1-right
  (λ (n m)
    (λ (add1-right-n-m)
      (cong add1-right-n-m (+ 1)))))

(define add1-right
  (λ (n m)
    (ind-Nat m
             (mot-add1-right n)
             (base-add1-right n)
             (step-add1-right n))))

(claim step-plusCommutative
       (Π ([n Nat]
           [m Nat])
          (-> (mot-plusCommutative n m)
              (mot-plusCommutative n (add1 m)))))

(claim mot-step-plusCommutative
       (-> Nat Nat Nat
           U))

(define mot-step-plusCommutative
  (λ (n m k)
    (= Nat
       k
       (add1 (+ m n)))))

(define step-plusCommutative
  (λ (n m)
    (λ (n+m=m+n)
      (replace (symm (add1-right m n))
               (mot-step-plusCommutative n m)
               (cong n+m=m+n (+ 1))))))

(define plusCommutative
  (λ (n m)
    (ind-Nat m
             (mot-plusCommutative n)
             (base-plusCommutative n)
             (step-plusCommutative n))))

;; Bonus

(claim step-plusCommutative-bonus
       (Π ([n Nat]
           [m Nat])
          (-> (mot-plusCommutative n m)
              (mot-plusCommutative n (add1 m)))))

(claim add1-left
       (Π ([n Nat]
           [m Nat])
          (= Nat
             (add1 (+ m n))
             (+ (add1 m) n))))

(define add1-left
  (λ (n m)
    (same (add1 (+ m n)))))

(define step-plusCommutative-bonus
  (λ (n m)
    (λ (n+m=m+n)
      (trans (trans (add1-right m n)
                    (cong n+m=m+n (+ 1)))
             (add1-left n m)))))
