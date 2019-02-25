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
