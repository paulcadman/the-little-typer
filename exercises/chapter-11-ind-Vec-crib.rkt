#lang pie

;; Exercises on ind-Vec from Chapter 11 of The Little Typer

;; Exercise 11.1
;;
;; Use ind-Vec to define a function called unzip that takes unzips
;; a vector of pairs into a pair of vectors.

(claim unzip
       (Π ([A U]
           [B U]
           [n Nat])
          (-> (Vec (Pair A B) n)
              (Pair (Vec A n) (Vec B n)))))

(claim mot-unzip
       (Π ([A U]
           [B U]
           [n Nat])
          (-> (Vec (Pair A B) n)
              U)))

(define mot-unzip
  (λ (A B n)
    (λ (_)
      (Pair (Vec A n) (Vec B n)))))

(claim base-unzip
       (Π ([A U]
           [B U])
          (Pair (Vec A zero) (Vec B zero))))

(define base-unzip
  (λ (A B)
    (cons vecnil vecnil)))

(claim step-unzip
       (Π ([A U]
           [B U]
           [k Nat]
           [h (Pair A B)]
           [t (Vec (Pair A B) k)])
          (-> (mot-unzip A B k t)
              (mot-unzip A B (add1 k) (vec:: h t)))))

(define step-unzip
  (λ (A B k h t)
    (λ (p)
      (cons (vec:: (car h) (car p))
            (vec:: (cdr h) (cdr p))))))

(define unzip
  (λ (A B n v)
    (ind-Vec n v
             (mot-unzip A B)
             (base-unzip A B)
             (step-unzip A B))))
