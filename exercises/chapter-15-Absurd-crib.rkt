#lang pie

;; Exercises on Absurd from Chapter 15 of The Little Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (_ b+a-k)
               (add1 b+a-k)))))

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

(claim =consequence
       (-> Nat Nat
           U))

(define =consequence
  (λ (n j)
    (which-Nat n
               (which-Nat j
                          Trivial
                          (λ (j-1)
                            Absurd))
               (λ (n-1)
                 (which-Nat j
                            Absurd
                            (λ (j-1)
                              (= Nat n-1 j-1)))))))

(claim =consequence-same
       (Π ([n Nat])
          (=consequence n n)))

(define =consequence-same
  (λ (n)
    (ind-Nat n
             (λ (k)
               (=consequence k k))
             sole
             (λ (n-1 =consequence-n-1)
               (same n-1)))))

(claim use-Nat=
       (Π ([n Nat]
           [j Nat])
          (-> (= Nat n j)
              (=consequence n j))))

(define use-Nat=
  (λ (n j)
    (λ (n=j)
      (replace n=j
               (λ (k)
                 (=consequence n k))
               (=consequence-same n)))))

(claim zero-not-add1
       (Π ([n Nat])
          (-> (= Nat zero (add1 n))
              Absurd)))

(define zero-not-add1
  (λ (n)
    (use-Nat= zero (add1 n))))

(claim sub1=
       (Π ([n Nat]
           [j Nat])
          (-> (= Nat (add1 n) (add1 j))
              (= Nat n j))))

(define sub1=
  (λ (n j)
    (use-Nat= (add1 n) (add1 j))))

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

;; Exercise 15.1
;;
;; State and prove that 3 is not less than 1.

(claim not-3<=1
       (-> (<= 3 1)
           Absurd))

(define not-3<=1
  (λ (three<=one)
    (zero-not-add1 (+ (car three<=one) 1)
                   (symm (trans (symm (add1-right 1
                                                  (car three<=one)))
                                (sub1= (+ (car three<=one) 2)
                                       0
                                       (trans (symm (add1-right 2 (car three<=one)))
                                              (cdr three<=one))))))))

;; Exercise 15.2
;;
;; State and prove that any natural number is not equal to its successor.

(claim n<>Sn
       (Π ([n Nat])
          (-> (= Nat n (add1 n))
              Absurd)))

(define n<>Sn
  (λ (n)
    (ind-Nat n
             (λ (k)
               (-> (= Nat k (add1 k))
                   Absurd))
             (zero-not-add1 0)
             (λ (n-1 n-1<>Sn-1)
               (λ (n=Sn)
                 (n-1<>Sn-1 (sub1= n-1
                                   (add1 n-1)
                                   n=Sn)))))))

;; Exercise 15.3
;;
;; State and prove that for every Nat n, the successor of n is not less than
;; or equal to n.

(claim Sn-not<=-n
       (Π ([n Nat])
          (-> (<= (add1 n) n)
              Absurd)))

(define Sn-not<=-n
  (λ (n)
    (ind-Nat n
             (λ (k)
               (-> (<= (add1 k) k)
                   Absurd))
             (λ (add1<=0)
               (zero-not-add1 (+ (car add1<=0) 0)
                              (symm (trans (symm (add1-right 0
                                                             (car add1<=0)))
                                           (cdr add1<=0)))))
             (λ (n-1 Sn-1-not<=-n-1)
               (λ (Sn<=n)
                 (Sn-1-not<=-n-1 (cons (car Sn<=n)
                                       (sub1= (+ (car Sn<=n) (add1 n-1)) n-1

                                              (trans (symm (add1-right (add1 n-1)
                                                                       (car Sn<=n)))
                                                     (cdr Sn<=n))))))))))

;; Exercise 15.4
;;
;; State and prove that 1 is not Even.

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

(claim one-not-Even
       (-> (Even 1)
           Absurd))

(define one-not-Even
  (λ (one_is_even)
    (ind-Either (n=0||n>0 (car one_is_even))
                (λ (_)
                  Absurd)
                (λ (n=0)
                  (zero-not-add1 0
                                 (symm (replace n=0
                                                (λ (k) (= Nat 1 (double k)))
                                                (cdr one_is_even)))))
                (λ (n>0)
                  (zero-not-add1 (double (car n>0))
                                 (sub1= 0
                                        (add1 (double (car n>0)))
                                        (replace (cdr n>0)
                                                 (λ (k)
                                                   (= Nat 1 (double k)))
                                                 (cdr one_is_even))))))))
