#lang pie

;; Exercises on ind-Nat from Chapter 10 of The Little Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (_ b+a-k)
               (add1 b+a-k)))))

(claim length
       (Π ([E U])
          (-> (List E)
              Nat)))

(define length
  (λ (_)
    (λ (es)
      (rec-List es
                0
                (λ (_ _ almost-length)
                  (add1 almost-length))))))

(claim step-append
       (Π ([E U])
          (-> E (List E) (List E)
              (List E))))

(define step-append
  (λ (E)
    (λ (e es append-es)
      (:: e append-es))))

(claim append
       (Π ([E U])
          (-> (List E) (List E)
              (List E))))

(define append
  (λ (E)
    (λ (start end)
      (rec-List start
                end
                (step-append E)))))

;; Exercise 10.1
;;
;; Define a function called list-length-append-dist that states and proves that
;; if you append two lists, l1 and l2, and then the length of the result is
;; equal to the sum of the lengths of l1 and l2.

(claim list-length-append-dist
       (Π ([E U]
           [l1 (List E)]
           [l2 (List E)])
          (= Nat
             (length E (append E l1 l2))
             (+ (length E l1) (length E l2)))))


;; Exercise 10.2
;;
;; In the following exercises we'll use the function called <= that takes two
;; Nat arguments a, b and evaluates to a type representing the proposition
;; that a is less than or equal to b.

(claim <=
       (-> Nat Nat
           U))

(define <=
  (λ (a b)
    (Σ ([k Nat])
       (= Nat (+ k a) b))))

;; Exercise 10.2.1
;;
;; Using <=, state and prove that 1 is less than or equal to 2.

;; Exercise 10.2.2
;;
;; Define a funciton called <=-simplify to state and prove that for all
;; Nats a, b, n we have that n+a <= b implies a <= b
;;
;; NB: You may need to use plusAssociative that was proved in Exercise 8.3.

(claim <=-simplify
       (Π ([a Nat]
           [b Nat]
           [n Nat])
          (-> (<= (+ n a) b)
              (<= a b))))

;; Exercise 10.2.3
;;
;; Define a function called <=-trans that states and proves that <= is
;; transitive.

(claim <=-trans
       (Π ([a Nat]
           [b Nat]
           [c Nat])
          (-> (<= a b)
              (<= b c)
              (<= a c))))
