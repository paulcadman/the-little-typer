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

;; The following is not required for the statement of exercises
;; but will be required in some solutions.

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

;; Exercise 15.1
;;
;; State and prove that 3 is not less than 1.

(claim not-3<=1
       (-> (<= 3 1)
           Absurd))

;; Exercise 15.2
;;
;; State and prove that any natural number is not equal to its successor.

(claim n<>Sn
       (Π ([n Nat])
          (-> (= Nat n (add1 n))
              Absurd)))

;; Exercise 15.3
;;
;; State and prove that for every Nat n, the successor of n is not less
;; than or equal to n.

(claim Sn-not<=-n
       (Π ([n Nat])
          (-> (<= (add1 n) n)
              Absurd)))

;; Exercise 15.4
;;
;; State and prove that 1 is not Even.

(claim one-not-Even
       (-> (Even 1)
           Absurd))
