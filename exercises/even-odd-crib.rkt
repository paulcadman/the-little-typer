#lang pie

;; Exercises on Even and Odd from Chapter 12 of The Little Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (_ a+b-1)
               (add1 a+b-1)))))

(claim double
       (-> Nat
           Nat))

(define double
  (λ (n)
    (rec-Nat n
             0
             (λ (_ n+n-2)
               (+ 2 n+n-2)))))

(claim Even
       (-> Nat
           U))

(define Even
  (λ (n)
    (Σ ([half Nat])
       (= Nat n (double half)))))

(claim Odd
       (-> Nat
           U))

(define Odd
  (λ (n)
    (Σ ([haf Nat])
       (= Nat n (add1 (double haf))))))

(claim <=
       (-> Nat Nat
           U))

(define <=
  (λ (a b)
    (Σ ([k Nat])
       (= Nat (+ k a) b))))

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

(claim k+0=k
       (Π ([k Nat])
          (= Nat (+ k 0) k)))

(define k+0=k
  (λ (k)
    (ind-Nat k
             (λ (x)
               (= Nat (+ x 0) x))
             (same 0)
             (λ (k-1)
               (λ (k-1+0=k-1)
                 (cong k-1+0=k-1 (+ 1)))))))

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

;; Exercise 12.1
;;
;; Define a function called sumOfTwoEvensIsEven that states and proves that the sum
;; of two Even Nats is Even.

(claim sumOfTwoEvensIsEven
       (Π ([n Nat]
           [m Nat])
          (-> (Even n) (Even m)
              (Even (+ n m)))))

(claim a=b/\c=d->a+c=b+d
       (Π ([a Nat]
           [b Nat]
           [c Nat]
           [d Nat])
          (-> (= Nat a b) (= Nat c d)
              (= Nat (+ a c) (+ b d)))))

(define a=b/\c=d->a+c=b+d
  (λ (a b c d)
    (λ (a=b c=d)
      (replace a=b
               (λ (x)
                 (= Nat (+ a c) (+ x d)))
               (cong c=d (+ a))))))

(claim double-a+double-b=double-a+b
       (Π ([a Nat]
           [b Nat])
          (= Nat (+ (double a) (double b))
             (double (+ a b)))))

(define double-a+double-b=double-a+b
  (λ (a b)
    (ind-Nat a
             (λ (x)
               (= Nat (+ (double x) (double b))
                  (double (+ x b))))
             (same (double b))
             (λ (_ double-n-1+double-b=double-n-1+b)
               (cong double-n-1+double-b=double-n-1+b (+ 2))))))

(define sumOfTwoEvensIsEven
  ;; Given n = double half_n
  ;;       m = double half_m
  ;;
  ;; By a=b/\c=d->a+c=b+d we have:
  ;;
  ;;   n + m = double half_n + double half_m  [1]
  ;;
  ;; And by double-a+double-b=double-a+b we have:
  ;;
  ;;  double half_n + double half_m = double (half_n + half_m) [2]
  ;;
  ;; We obtain:
  ;;
  ;;   n + m = double (half_n + half_m)
  ;;
  ;; By using trans with [1] and [2]
  (λ (n m)
    (λ (even-n even-m)
      (cons (+ (car even-n) (car even-m))
            (trans (a=b/\c=d->a+c=b+d n
                                      (double (car even-n))
                                      m
                                      (double (car even-m))
                                      (cdr even-n)
                                      (cdr even-m))
                   (double-a+double-b=double-a+b (car even-n)
                                                 (car even-m)))))))

;; Exercise 12.2
;;
;; Define a function called sumOfTwoOddsIsEven that states and proves that the sum of
;; two Odd Nats is Even.

(claim sumOfTwoOddsIsEven
       (Π ([n Nat]
           [m Nat])
          (-> (Odd n) (Odd m)
              (Even (+ n m)))))

(define sumOfTwoOddsIsEven
  ;; Given n = 1 + double haf_n
  ;;       m = 1 + double haf_m
  ;;
  ;; By a=b/\c=d->a+c=b+d we have:
  ;;
  ;;   n + m = 1 + double haf_n + 1 + double haf_m  [1]
  ;;
  ;; Use trans to combine this with add1-right to get
  ;;
  ;;   n + m = 2 + double haf_n + double haf_m [2]
  ;;
  ;; And by double-a+double-b=double-a+b we have:
  ;;
  ;;  double haf_n + double haf_m = double (haf_n + haf_m) [3]
  ;;
  ;; Using cong we obtain:
  ;;
  ;;  2 + double haf_n + double haf_m = 2 + double (haf_n + haf_m) [4]
  ;;
  ;; The right hand side is judgementally equal to double (1 + haf_n + haf_m)
  ;; which gives:
  ;;
  ;;  2 + double haf_n + double haf_m = double (haf_n + haf_m) [5]
  ;;
  ;; We obtain:
  ;;
  ;;   n + m = double (1 + half_n + half_m)
  ;;
  ;; By using trans with [2] and [4] and judgemental equality [5]
  (λ (n m)
    (λ (odd-n odd-m)
      (cons (+ 1 (+ (car odd-n) (car odd-m)))
            (trans (trans (a=b/\c=d->a+c=b+d n
                                             (add1 (double (car odd-n)))
                                             m
                                             (add1 (double (car odd-m)))
                                             (cdr odd-n)
                                             (cdr odd-m))
                          (add1-right (double (car odd-m))
                                      (+ 1 (double (car odd-n)))))
                   (cong (double-a+double-b=double-a+b (car odd-n)
                                                       (car odd-m))
                         (+ 2)))))))


;; Exercise 12.3
;;
;; Define a function called nOrSuccnIsEven that states and proves that for all Nats n, either
;; n is Even or n+1 is Even.

(claim nOrSuccnIsEven
       (Π ([n Nat])
          (Either (Even n) (Even (add1 n)))))

(define nOrSuccnIsEven
  ;;
  ;; Induction on n
  ;;
  ;; For the ind-Either step
  ;;
  ;; If we are given that n-1 is even then 1 + n-1 is odd so 1 + (1 + n-1) is even.
  ;;
  ;; If we are given that 1 + n-1 is even then we are done.
  (λ (n)
    (ind-Nat n
             (λ (x)
               (Either (Even x) (Even (add1 x))))
             (left (cons 0 (same 0)))
             (λ (n-1)
               (λ (n-1-even||n-even)
                 (ind-Either n-1-even||n-even
                             (λ (_)
                               (Either (Even (add1 n-1)) (Even (add1 (add1 n-1)))))
                             (λ (n-1-even)
                               (right
                                (sumOfTwoEvensIsEven 2 n-1 (cons 1 (same 2)) n-1-even)))
                             (λ (n-even)
                               (left n-even))))))))

;; Exercise 12.4
;;
;; Define a function called either-a<=b-or-b<=a that states and proves that for all Nats a b,
;; either a<=b or b<=a

(claim either-a<=b-or-b<=a
       (Π ([a Nat]
           [b Nat])
          (Either (<= a b) (<= b a))))

(claim a<=b/\car=0->a=b
       (Π ([a Nat]
           [b Nat]
           [a<=b (<= a b)])
          (-> (= Nat (car a<=b) 0)
              (= Nat a b))))

(define a<=b/\car=0->a=b
  (λ (a b a<=b)
    (λ (car-a<=b==0)
      (replace car-a<=b==0
               (λ (x)
                 (= Nat (+ x a) b))
               (cdr a<=b)))))

(claim n=0||n>0
       (Π ([n Nat])
          (Either (= Nat n 0)
                  (Σ ([k Nat])
                     (= Nat n (add1 k))))))

(define n=0||n>0
  (λ (n)
    (ind-Nat n
             (λ (x)
               (Either (= Nat x 0)
                       (Σ ([k Nat])
                          (= Nat x (add1 k)))))
             (left (same 0))
             (λ (n-1 n-1=0||n-1>0)
               (ind-Either n-1=0||n-1>0
                           (λ (x)
                             (Either (= Nat (add1 n-1) 0)
                                     (Σ ([k Nat])
                                        (= Nat (add1 n-1) (add1 k)))))
                           (λ (n-1=0)
                             (right (cons 0 (cong n-1=0 (+ 1)))))
                           (λ (n-1>0)
                             (right (cons (add1 (car n-1>0))
                                          (cong (cdr n-1>0) (+ 1))))))))))

(claim a<=b-a=b||a<b
       (Π ([a Nat]
           [b Nat]
           [a<=b (<= a b)])
          (Either (= Nat a b)
                  (Σ ([k Nat])
                     (= Nat (car a<=b) (add1 k))))))

(define a<=b-a=b||a<b
  (λ (a b a<=b)
    (ind-Either (n=0||n>0 (car a<=b))
                (λ (x)
                  (Either (= Nat a b)
                          (Σ ([k Nat])
                             (= Nat (car a<=b) (add1 k)))))
                (λ (n=0)
                  (left (a<=b/\car=0->a=b a
                                          b
                                          a<=b
                                          n=0)))
                (λ (n>0)
                  (right n>0)))))

(claim a<b->1+a<=b
       (Π ([a Nat]
           [b Nat]
           [a<=b (<= a b)])
          (-> (Σ ([k Nat])
                 (= Nat (car a<=b) (add1 k)))
              (<= (add1 a) b))))

(define a<b->1+a<=b
  (λ (a b a<=b)
    (λ (car-a<=b=1+k)
      (cons (car car-a<=b=1+k)
            (trans (trans  (add1-right a
                                       (car car-a<=b=1+k))
                           (plusAssociative (car car-a<=b=1+k)
                                            a
                                            1))
                   (replace (cdr car-a<=b=1+k)
                            (λ (x)
                              (= Nat (+ x a) b))
                            (cdr a<=b)))))))

(define either-a<=b-or-b<=a
  (λ (a b)
    (ind-Nat a
             (λ (x)
               (Either (<= x b) (<= b x)))
             (left (cons b (k+0=k b)))
             (λ (n-1)
               (λ (n-1<=b-or-b<=n-1)
                 (ind-Either n-1<=b-or-b<=n-1
                             (λ (x)
                               (Either (<= (add1 n-1) b)
                                       (<= b (add1 n-1))))
                             (λ (n-1<=b)
                               (ind-Either (a<=b-a=b||a<b n-1
                                                          b
                                                          n-1<=b)
                                           (λ (x)
                                             (Either (<= (add1 n-1) b)
                                                     (<= b (add1 n-1))))
                                           (λ (n-1=b)
                                             (right (cons 1
                                                          (cong (symm n-1=b)
                                                                (+ 1)))))
                                           (λ (n-1<b)
                                             (left (a<b->1+a<=b n-1
                                                                b
                                                                n-1<=b
                                                                n-1<b)))))
                             (λ (b<=n-1)
                               (right (cons (+ 1 (car b<=n-1))
                                            (cong (cdr b<=n-1)
                                                  (+ 1)))))))))))
