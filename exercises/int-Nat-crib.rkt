#lang pie

;; Exercises on Vec and ind-Nat from Chapters 6 and 7 of The Little
;; Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (a-k b+a-k)
               (add1 b+a-k)))))

;; Exercise 7.0
;;
;; Define a function called zip that takes an argument of type (Vec A n) and a
;; second argument of type (Vec B n) and evaluates to a vlue of type (Vec (Pair A B) n),
;; the result of zipping the first and second arguments.

(claim zip
       (Π ([A U]
           [B U]
           [n Nat])
          (-> (Vec A n) (Vec B n)
              (Vec (Pair A B) n))))

(claim mot-zip
       (-> U U Nat
           U))

(define mot-zip
  (λ (A B n)
    (-> (Vec A n) (Vec B n)
        (Vec (Pair A B) n))))

(claim base-zip
       (Π ([A U]
           [B U])
          (-> (Vec A 0) (Vec B 0)
              (Vec (Pair A B) 0))))

(define base-zip
  (λ (A B)
    (λ (_ _)
      vecnil)))

(claim step-zip
       (Π ([A U]
           [B U]
           [n Nat])
          (-> (mot-zip A B n)
              (mot-zip A B (add1 n)))))

(define step-zip
  (λ (A B n)
    (λ (zip-n)
      (λ (es fs)
        (vec:: (cons (head es) (head fs))
               (zip-n (tail es) (tail fs)))))))

(define zip
  (λ (A B n)
    (ind-Nat n
             (mot-zip A B)
             (base-zip A B)
             (step-zip A B))))

(check-same (Vec (Pair Nat Atom) 2)
            (zip Nat Atom 2
                 (vec:: 1 (vec:: 2 vecnil))
                 (vec:: 'orange (vec:: 'pear vecnil)))
            (vec:: (cons 1 'orange) (vec:: (cons 2 'pear) vecnil)))

;; Exercise 7.1
;;
;; Define a function called append that takes an argument of type (Vec E n) and an
;; argument of type (Vect E m) and evaluates to a value of type (Vec (+ n m)), the
;; result of appending the elements of the second argument to the end of the first.

(claim append
       (Π ([E U]
           [n Nat]
           [m Nat])
          (-> (Vec E n) (Vec E m)
              (Vec E (+ n m)))))

(claim mot-append
       (-> U Nat Nat
           U))

(define mot-append
  (λ (E m n)
    (-> (Vec E n) (Vec E m)
        (Vec E (+ n m)))))

(claim base-append
       (Π ([E U]
           [n Nat])
          (-> (Vec E zero) (Vec E n)
              (Vec E n))))

(define base-append
  (λ (E n)
    (λ (_ es)
      es)))

(claim step-append
       (Π ([E U]
           [n Nat]
           [l Nat])
          (-> (mot-append E n l)
              (mot-append E n (add1 l)))))

(define step-append
  (λ (E n l)
    (λ (append-l)
      (λ (ls ns)
        (vec:: (head ls) (append-l (tail ls) ns))))))

(define append
  (λ (E n m)
    (ind-Nat n
             (mot-append E m)
             (base-append E m)
             (step-append E m))))

(check-same (Vec Nat 5)
            (append Nat 2 3
                    (vec:: 0 (vec:: 1 vecnil))
                    (vec:: 2 (vec:: 3 (vec:: 4 vecnil))))
            (vec:: 0 (vec:: 1 (vec:: 2 (vec:: 3 (vec:: 4 vecnil))))))

;; Exercise 7.2
;;
;; Define a function called drop-last-k that takes an argument of type (Vec E ?) and
;; evaluates to a value of type (Vec E ?), the result of dropping the last k elements
;; from the first argument.
;;
;; NB: The type of the function should guarantee that we can't drop more elements
;; than there are in the first argument.

(claim drop-last-k
       (Π ([E U]
           [k Nat]
           [n Nat])
           (-> (Vec E (+ n k))
               (Vec E n))))

(claim mot-drop-last-k
       (-> U Nat Nat
           U))

(define mot-drop-last-k
    (λ (E k n)
      (-> (Vec E (+ n k))
          (Vec E n))))

(claim base-drop-last-k
       (Π ([E U]
           [k Nat])
          (-> (Vec E k)
              (Vec E zero))))

(define base-drop-last-k
  (λ (E k)
    (λ (_)
      vecnil)))

(claim step-drop-last-k
       (Π ([E U]
           [k Nat]
           [l Nat])
          (-> (mot-drop-last-k E k l)
              (mot-drop-last-k E k (add1 l)))))

(define step-drop-last-k
  (λ (E k l)
    (λ (drop-last-k-l)
      (λ (es)
        (vec:: (head es) (drop-last-k-l (tail es)))))))

(define drop-last-k
  (λ (E k n)
    (ind-Nat n
             (mot-drop-last-k E k)
             (base-drop-last-k E k)
             (step-drop-last-k E k))))

(check-same (Vec Nat 1)
            (drop-last-k Nat 2 1
                         (vec:: 0 (vec:: 1 (vec:: 2 vecnil))))
            (vec:: 0 vecnil))
