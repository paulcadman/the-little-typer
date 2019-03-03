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

(claim filter-list
       (Π ([E U])
          (-> (-> E Nat) (List E)
              (List E))))

(claim filter-list-step
       (Π ([E U])
          (-> (-> E Nat)
              (-> E (List E) (List E)
                  (List E)))))

(claim if
       (Π ([A U])
          (-> Nat A A
              A)))

(define if
  (λ (A)
    (λ (e if-then if-else)
      (which-Nat e
                 if-else
                 (λ (_) if-then)))))

(define filter-list-step
  (λ (E)
    (λ (p)
      (λ (e es filtered-es)
        (if (List E) (p e)
            (:: e filtered-es)
            filtered-es)))))

(define filter-list
  (λ (E)
    (λ (p es)
      (rec-List es
                (the (List E) nil)
                (filter-list-step E p)))))

;; Additional proof from previous exercises:

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

;; Prove by induction on l1

(claim base-list-length-append-dist
       (Π ([E U]
           [l2 (List E)])
          (= Nat
             (length E (append E nil l2))
             (+ (length E nil) (length E l2)))))

(define base-list-length-append-dist
  (λ (E l2)
    (same (length E l2))))

(claim mot-list-length-append-dist
       (Π ([E U]
           [l2 (List E)])
          (-> (List E)
              U)))

(define mot-list-length-append-dist
  (λ (E l2 l)
    (= Nat
       (length E (append E l l2))
       (+ (length E l) (length E l2)))))

(claim step-list-length-append-dist
       (Π ([E U]
           [l2 (List E)]
           [e E]
           [es (List E)])
          (-> (mot-list-length-append-dist E l2 es)
              (mot-list-length-append-dist E l2 (:: e es)))))

(define step-list-length-append-dist
  (λ (E l2 e es)
    (λ (length--l2-es=length-l2+length-es)
      (cong length--l2-es=length-l2+length-es (+ 1)))))

(define list-length-append-dist
  (λ (E l1 l2)
    (ind-List l1
              (mot-list-length-append-dist E l2)
              (base-list-length-append-dist E l2)
              (step-list-length-append-dist E l2))))

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

(claim one<=two
       (<= 1 2))

(define one<=two
  (cons 1 (same 2)))

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

(define <=-simplify
  (λ (a b n)
    (λ (n+a<=b)
      (cons (+ (car n+a<=b) n)
            ;;
            ;; The goal is to produce a value of type:
            ;;
            ;; [1] (= Nat (+ (+ (car n+a<=b) n) a)
            ;;               b)
            ;;
            ;; (cdr n+a<=b) is a value of type:
            ;;
            ;; [2] (= Nat (+ (car n+a<=b) (+ n a))
            ;;            b)
            ;;
            ;; Using symm and plusAssociative we produce a value of type:
            ;;
            ;; [3] (= Nat (+ (+ (car n+a<=b) n) a)
            ;;            (+ (car n+a<=b) (+ n a)))
            ;;
            ;; Using trans with [2] and [3] we produce a value of [1] which
            ;; is our goal.
            ;;
            (trans (symm (plusAssociative n a (car n+a<=b)))
                   (cdr n+a<=b))))))

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

(define <=-trans
  ;;
  ;; The goal is to produce a value of type:
  ;;
  ;; [1] (<= a c)
  ;;
  ;; The target of the replace has type:
  ;;
  ;; [2] (= Nat b (+ (car a<=b) a))
  ;;
  ;; (mot from) is therefore (mot b) and its type is:
  ;;
  ;; [3] (Σ ([k Nat])
  ;;        (= Nat (+ k b) c))
  ;;
  ;; b<=c is a value of [3] so it can be used as the base of reduce.
  ;;
  ;; The replace expression therefore produces a value of type (mot to) which is
  ;; (mot (+ (car a<=b) a)). This has type:
  ;;
  ;; [4] (Σ ([k] Nat)
  ;;        (= Nat (+ k (+ (car a<=b) a )) c))
  ;;
  ;; By definition of <= this is the same type as:
  ;;
  ;; [5] (<= (+ (car a<=b) a) c)
  ;;
  ;; Using <=-simplify we can remove (car a<=b) from [5] to produce a value of
  ;; [1], our goal type.
  ;;
  (λ (a b c)
    (λ (a<=b b<=c)
      (<=-simplify a c (car a<=b)
                   (replace (symm (cdr a<=b))
                            (λ (l)
                              (Σ ([k Nat])
                                 (= Nat (+ k l) c)))
                            b<=c)))))

;; Exercise 10.3
;;
;; Define a function called length-filter-list that states and proves that
;; filtering a list (in the sense of filter-list from Exercise 5.3) evaluates
;; to a a list no longer than the original list.

(claim length-filter-list
       (Π ([E U]
           [l (List E)]
           [p (-> E Nat)])
          (<= (length E (filter-list E p l))
              (length E l))))

(claim base-length-filter-list
       (Π ([E U]
           [p (-> E Nat)])
          (<= (length E (filter-list E p nil))
              (length E nil))))

(define base-length-filter-list
  (λ (E p)
    (cons 0 (same 0))))

(claim mot-length-filter-list
       (Π ([E U]
           [p (-> E Nat)])
          (-> (List E)
              U)))

(define mot-length-filter-list
  (λ (E p)
    (λ (l)
      (<= (length E (filter-list E p l))
          (length E l)))))

(claim step-length-filter-list
       (Π ([E U]
           [p (-> E Nat)]
           [e E]
           [es (List E)])
          (-> (mot-length-filter-list E p es)
              (mot-length-filter-list E p (:: e es)))))

;; Prove that if we conditionally cons an element to a list
;; then the resulting list is no longer that if we always cons
;; the element to the list.

(claim length-conditional-cons
       (Π ([E U]
           [l (List E)]
           [e E]
           [k Nat])
          (<= (length E (if (List E) k
                            (:: e l)
                            l))
              (length E (:: e l)))))

;; prove this by induction on k

(claim mot-length-conditional-cons
       (Π ([E U]
           [l (List E)]
           [e E])
          (-> Nat
              U)))

(define mot-length-conditional-cons
  (λ (E l e)
    (λ (k)
      (<= (length E (if (List E) k
                        (:: e l)
                        l))
          (length E (:: e l))))))

(claim base-length-conditional-cons
       (Π ([E U]
           [l (List E)]
           [e E])
          (<= (length E l)
              (length E (:: e l)))))

(define base-length-conditional-cons
  (λ (E l e)
    (cons 1 (same (length E (:: e l))))))

(claim step-length-conditional-cons
       (Π ([E U]
           [l (List E)]
           [e E]
           [k Nat])
          (-> (mot-length-conditional-cons E l e k)
              (mot-length-conditional-cons E l e (add1 k)))))

(define step-length-conditional-cons
  (λ (E l e k)
    (λ (_)
      ;;
      ;; The goal is to produce a value of type:
      ;;
      ;; [1] (<= (length E (if (List E)
      ;;                       (add1 k)
      ;;                       (:: e l)
      ;;                       l))
      ;;         (length E (:: e l)))
      ;;
      ;; Since the target of the if expression, (add1 k), uses
      ;; the add1 constructor then the (:: e l) branch is always selected.
      ;;
      ;; The type of [1] is therefore the same as:
      ;;
      ;; [2] (<= (length E (:: e l))
      ;;         (length E (:: e l)))
      ;;
      (cons 0 (same (length E (:: e l)))))))

(define length-conditional-cons
  (λ (E l e k)
    (ind-Nat k
             (mot-length-conditional-cons E l e)
             (base-length-conditional-cons E l e)
             (step-length-conditional-cons E l e))))


(claim <=-cong-add1
       (Π ([a Nat]
           [b Nat])
          (-> (<= a b)
              (<= (+ 1 a) (+ 1 b)))))

(define <=-cong-add1
  (λ (a b)
    (λ (a<=b)
      (cons (car a<=b)
            ;; The goal is to find a value of type:
            ;;
            ;;     (= Nat (+ (car a<=b) (add1 a))
            ;;            (add1 b))
            ;;
            ;; cong produces a value of type:
            ;;
            ;; [1]    (= Nat (add1 (+ (car a<=b) a))
            ;;               (add1 b))
            ;;
            ;; Use (add1-right a (car a<=b)) to produce a value of type:
            ;;
            ;; [2]    (= Nat (+ (car a<=b) (add1 a))
            ;;               (add1 (+ (car a<=b) a)))
            ;;
            ;; Then use trans to combine [1] and [2] together to produce
            ;; a value of the goal type.
            (trans (add1-right a (car a<=b))
                   (cong (cdr a<=b) (+ 1)))))))

(define step-length-filter-list
  ;;
  ;; The goal is to find a value of type:
  ;;
  ;; [1] (<= (length E (filter-list E p (:: e es)))
  ;;         (length E (:: e es)))
  ;;
  ;; By definition [1] is the same type as:
  ;;
  ;; [2] (<= (length E (if (List E) (p e)
  ;;                                (:: e (filter-list E p es))
  ;;                                (filter-list E p es)))
  ;;         (+ 1 (length E es)))
  ;;
  ;; length-conditional-cons is used to produce a value of type:
  ;;
  ;; [3] (<= (length E (if (List E) (p e)
  ;;                                (:: e (filter-list E p es))
  ;;                                (filter-list E p es)))
  ;;         (length E (:: e (filter-list E p es))))
  ;;
  ;; By definition [3] is the same type as:
  ;;
  ;; [4] (<= (length E (if (List E) (p e)
  ;;                                (:: e (filter-list E p es))
  ;;                                (filter-list E p es)))
  ;;         (+ 1 (length E (filter-list E p es))))
  ;;
  ;; Using the induction hypothesis filtered-es<=es <=-cong-add1
  ;; produces a value of type:
  ;;
  ;; [5] (<= (+ 1 (length E (filter-list E p es)))
  ;;         (+ 1 (length E es)))
  ;;
  ;; So using <=-trans on [3] and [5] together with the definitional
  ;; equalities produces a value of the goal type.
  ;;
  (λ (E p e es)
    (λ (filtered-es<=es)
      (<=-trans (length E (filter-list E p (:: e es)))
                (length E (:: e (filter-list E p es)))
                (length E (:: e es))
                (length-conditional-cons E
                                         (filter-list E p es)
                                         e
                                         (p e))
                (<=-cong-add1 (length E (filter-list E p es))
                              (length E es)
                              filtered-es<=es)))))

(define length-filter-list
  (λ (E l p)
    (ind-List l
              (mot-length-filter-list E p)
              (base-length-filter-list E p)
              (step-length-filter-list E p))))
