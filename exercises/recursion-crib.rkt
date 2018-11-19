#lang racket

#| "An understanding of recursive functions over non-nested lists and non-negative numbers is all you need to understand
this book" p.xi
|#

;; p.xii
(define atom?
  (lambda (x)
    (and (not (pair? x)) (not (null? x)))))

;; p.16
;; list of atoms
(define lat?
  (lambda (l)
    (cond
      ((null? l) #t)
      ((atom? (car l)) (lat? (cdr l)))
      (else #f))))

;; write a length function
;; (mylength '('a 'b 'c)) => 3
(define mylength
  (lambda (l)
    (cond
      ((null? l) 0)
      (else (+ 1 (mylength (cdr l)))))))

;; write an iota function
;; (iota 2 6) => '(2, 3, 4, 5, 6)
(define iota
  (lambda (n m)
    (cond
      ((> n m) '())
      (else (cons n (iota (+ 1 n) m))))))

;; write a function to check membership
;; (member? 'a '(a b c)) => #t
;;
;; What's the value of (member? 'a '('a 'b 'c)) ?
(define member?
  (lambda (a lat)
    (cond
      ((null? lat) #f)
      (else (or (eq? (car lat) a)
                (member? a (cdr lat)))))))

;; write a function to remove the first occurance of a member from a list
;; (rember 'a '(a b c a)) => '(b c a)
(define rember
  (lambda (a lat)
    (cond
      ((null? lat) '())
      ((eq? (car lat) a) (cdr lat))
      (else (cons (car lat) (rember a (cdr lat)))))))

;; write a function insertR that inserts an atom
;; to the right of another in a list
;;  (insertR '(c b b) 'b 'a) => '(c b a b)
(define insertR
  (lambda (l old new)
    (cond
      ((null? l) '())
      ((eq? (car l) old) (cons old (cons new (cdr l))))
      (else (cons (car l) (insertR (cdr l) old new))))))

;; write a function insertL that inserts an atom to the left
;; of another in a list
;;  (insertL '(c b b) 'b 'a) => '(a b b)
(define insertL
  (lambda (l old new)
    (cond
      ((null? l) '())
      ((eq? (car l) old) (cons new l))
      (else (cons car l) (insertL (cdr l) old new)))))

;; write a function that replaces the first occurance of
;; an atom in a list with another
;;  (subst 'z 'a '(a b c)) => '(z b c)
(define subst
  (lambda (new old lat)
    (cond
      ((null? lat) '())
      ((eq? (car lat) old) (cons new (cdr lat)))
      ((cons (car lat) (subst new old (cdr lat)))))))

;; write a function that removes all occurances of an
;; atom from a list
;;  (multirember 'a '(a b a c)) => '(b c)
(define multirember
  (lambda (a lat)
    (cond
      ((null? lat) '())
      ((eq? (car lat) a) (multirember a (cdr lat)))
      (else (cons (car lat) (multirember a (cdr lat)))))))

;; write a function insertR that inserts an atom
;; to the right of all occurances of another in a list
;;  (multiinsertR 'z 'a '(a b a c a)) => '(a z b a z c a z)
(define multiinsertR
  (lambda (new old lat)
    (cond
      ((null? lat) '())
      ((eq? (car lat) old) (cons old (cons new (multiinsertR new old (cdr lat)))))
      (else (cons (car lat) (multiinsertR new old (cdr lat)))))))

;; write a function multisubst that replaces all occurances
;; of an atom with another in a list
;;  (multisubst 'z 'a '(b c a z d a)) => '(b c z z d z)
(define multisubst
  (lambda (new old lat)
    (cond
      ((null? lat) '())
      ((eq? old (car lat)) (cons new (multisubst new old (cdr lat))))
      (else (cons (car lat) (multisubst new old (cdr lat)))))))

(define add1
  (lambda (n)
    (+ n 1)))

(define sub1
  (lambda (n)
    (- n 1)))

;; write a function o+ that adds two numbers (using add1, sub1)
;; (o+ 2 3) => 5
(define o+
  (lambda (n m)
    (cond
      ((zero? m) n)
      (else (add1 (o+ n (sub1 m)))))))

;; write a function o- that subtract two numbers (using add1, sub1)
;;  (o- 3 2) => 1
(define o-
  (lambda (n m)
    (cond
      ((zero? m) n)
      (else (sub1 (o- n (sub1 m)))))))

;; write a function that adds all the numbers in a tuple
;;  (addtup '(1 2 3)) => 6
(define addtup
  (lambda (tup)
    (cond
      ((null? tup) 0)
      (else (o+ (car tup) (addtup (cdr tup)))))))

;; write a function to multiply two numbers
;;  (ox 2 3) => 6
(define ox
  (lambda (n m)
    (cond
      ((zero? m) 0)
      (else (o+ n (ox n (sub1 m)))))))

;; write a function which defines 'greater than' for two numbers
;;  (> 2 3) => #f
(define >
  (lambda (n m)
    (cond
      ((zero? n) #f)
      ((zero? m) #t)
      (else (> (sub1 n) (sub1 m))))))
