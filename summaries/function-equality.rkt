#lang pie

;; It's possible to define plus using rec-Nat
;; by eliminated by the first or second arguments
(claim plus-elim-first (-> Nat Nat
             Nat))

(define plus-elim-first
  (λ (n m)
    (rec-Nat n
             m
             (λ (n-1 n-1+m)
               (add1 n-1+m)))))

(check-same Nat (plus-elim-first 0 0) 0)
(check-same Nat (plus-elim-first 0 1) 1)
(check-same Nat (plus-elim-first 1 0) 1)
(check-same Nat (plus-elim-first 1 1) 2)
(check-same Nat (plus-elim-first 2 3) 5)

(claim plus-elim-second (-> Nat Nat
                            Nat))

(define plus-elim-second
  (λ (n m)
    (rec-Nat m
             n
             (λ (m-1 m-1+n)
               (add1 m-1+n)))))

(check-same Nat (plus-elim-second 0 0) 0)
(check-same Nat (plus-elim-second 0 1) 1)
(check-same Nat (plus-elim-second 1 0) 1)
(check-same Nat (plus-elim-second 1 1) 2)
(check-same Nat (plus-elim-second 2 3) 5)

(claim curried-elim-first (-> Nat Nat))
(define curried-elim-first
  (λ (n)
    ((plus-elim-first n) 1)))

;; (claim +three (-> Nat Nat))
;; (define +three (+ 1))

(claim curried-elim-second (-> Nat Nat))
(define curried-elim-second
  (λ (n)
    ((plus-elim-second n) 1)))

; The functions we get by currying using plus elimiated by the first and second argument
; are different (one has an elimiator in the body)
;
; The expressions
;   (λ (n)
;     (rec-Nat n
;        (the Nat 1)
;        (λ (n-1 n-1+m)
;          (add1 n-1+m))))
; and
;   (λ (n)
;     (add1 n))
; are not the same
;   (→ Nat
;     Nat)
(check-same (-> Nat Nat) curried-elim-first curried-elim-second)
