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

;; write an iota function
;; (iota 2 6) => '(2, 3, 4, 5, 6)

;; write a function to check membership
;; (member? 'a '(a b c)) => #t
;;
;; What's the value of (member? 'a '('a 'b 'c)) ?

;; write a function to remove the first occurance of a member from a list
;; (rember 'a '(a b c a)) => '(b c a)

;; write a function insertR that inserts an atom
;; to the right of another in a list
;;  (insertR '(c b b) 'b 'a) => '(c b a b)

;; write a function insertL that inserts an atom to the left
;; of another in a list
;;  (insertL '(c b b) 'b 'a) => '(a b b)

;; write a function that replaces the first occurance of
;; an atom in a list with another
;;  (subst 'z 'a '(a b c)) => '(z b c)

;; write a function that removes all occurances of an
;; atom from a list
;;  (multirember 'a '(a b a c)) => '(b c)

;; write a function insertR that inserts an atom
;; to the right of all occurances of another in a list
;;  (multiinsertR 'z 'a '(a b a c a)) => '(a z b a z c a z)

;; write a function multisubst that replaces all occurances
;; of an atom with another in a list
;;  (multisubst 'z 'a '(b c a z d a)) => '(b c z z d z)

(define add1
  (lambda (n)
    (+ n 1)))

(define sub1
  (lambda (n)
    (- n 1)))

;; write a function o+ that adds two numbers (using add1, sub1)
;;  (o+ 2 3) => 5

;; write a function o- that subtract two numbers (using add1, sub1)
;;  (o- 3 2) => 1

;; write a function that adds all the numbers in a tuple
;;  (addtup '(1 2 3)) => 6

;; write a function to multiply two numbers
;;  (ox 2 3) => 6

;; write a function which defines 'greater than' for two numbers
;;  (> 2 3) => #f
