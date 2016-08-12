#lang racket

; Compiles a propositional expression for short-circuit evaluation
; 0. Syntax (not checked) - an S-exp
;    a. x corresponds to referencing a boolean value.
;    b. (not exp), (and exp1 exp2), and (or exp1 exp2)
; 1. A boolean expression has its references counted.  These references
;    are implicitly numbered starting from 0.  References are indicated by x.
; 2. Compiled to a branching program like lab 3 fall 12 EXCEPT that compilation is
;    right-before-left for and/or.
; 3. The program is applied to a lat with T, F, and D values to be matched up with the x's.  
;    Conceptually, these are numbered left-to-right starting with 0 - which also maps to the
;    instruction's addresses.
; 4. Exactly one of the entire expression's true and false destinations must be an address equal
;    to the number of references.  The convention is to make this the true destination.

(struct instruction (addr op dest1 dest2))

; Tests for legal simple expression, from http://ranger.uta.edu/~weems/NOTES3302/LAB2SPR13/lab2spr13.symbol.rkt
(define (first x) (car x))

(define (second x) (car (cdr x)))

(define (exp? x)
  (cond
    ((eq? x 'x) #t)
    ((not (pair? x)) #f)
    ((eq? (first x) 'not) (and (pair? (cdr x))
                               (exp? (second x))
                               (null? (cdr (cdr x)))))
    ((eq? (first x) 'or) (and (expList? (cdr x))
                              (= (length (cdr x)) 2)))
    ((eq? (first x) 'and) (and (expList? (cdr x))
                               (= (length (cdr x)) 2)))
    ((eq? (first x) 'if) (and (expList? (cdr x))(= (length (cdr x)) 2)))
    (else #f)))

; Tests arguments to boolean operators or and and, from http://ranger.uta.edu/~weems/NOTES3302/LAB2SPR13/lab2spr13.symbol.rkt
(define (expList? x)
  (cond
    ((not (pair? x)) #f)
    ((exp? (car x)) (or (null? (cdr x))
                        (expList? (cdr x))))
    (else #f)))

(define (operandCount exp) ; Just counts the references, i.e. x
  (cond
    ((null? exp) 0)
    ((pair? exp) (+ (operandCount (car exp)) (operandCount (cdr exp))))
    ((eq? exp 'x) 1)
    (else 0)))

(define (compile exp)
  (define current (operandCount exp)) ; For numbering each x, always has number of last processed x.
  
  (define (helper exp trueDest falseDest) ; If exp evaluates true then goto trueDest, else falseDest.
    
    (cond
    
      ( (eq? exp 'x)
        
       (set! current (- current 1)) ; next x will be to the left - so decrement
      
       (cond ; compile appropriately for "fall through" if branch is not taken
         ((= (+ 1 current) trueDest)
          (list (instruction current 'brF falseDest -1)))  ; trueDest is the next instruction
         ((= (+ 1 current) falseDest)
          (list (instruction current 'brT trueDest -1)))
         (else 
          (list (instruction current 'br2 trueDest falseDest)))))
     
        ; falseDest is the next instruction
      ((eq? (car exp) 'not) ; just swaps the false and true destinations
       (helper (cadr exp) falseDest trueDest))
      ((eq? (car exp) 'if)
       (cond ((> (length (cdr exp)) 2)
             (let 
                 ((right (helper (last(cdr exp)) trueDest falseDest)))
               (append (helper (reverse(cdr (reverse exp))) trueDest falseDest) right)))
             (else
              (let ((right (helper (last(cdr exp)) trueDest falseDest)))
                   (append (helper (first(cdr exp)) current (+ 2 current)) right)))))
             
      ((eq? (car exp) 'and)
       (cond ((> (length (cdr exp)) 2)
       (let 
           
           ((right (helper (last(cdr exp)) trueDest falseDest))) ; first operand was true
         
         (append (helper (reverse (cdr(reverse exp))) current falseDest)       ; still need second operand true
                 right)))
             
             (else
              (let ((right (helper (last(cdr exp)) trueDest falseDest)))
                   (append (helper (first(cdr exp)) current falseDest) right)))))
      
      ((eq? (car exp) 'or)
       (cond ((> (operandCount (cdr exp)) 2)
       (let 
           ((right (helper (last (cdr exp)) trueDest falseDest))) ; first operand was false
         (append (helper  (reverse (cdr(reverse exp))) trueDest current)        ; second chance to get second operand true
                 right)))
              (else (let ((right (helper (last(cdr exp)) trueDest falseDest)))
                   (append (helper (first(cdr exp)) trueDest current) right)))))
      (else "syntax error")))
 
       
       
  (helper exp current (+ 1 current)))

(define (listing code)
  (cond
    ((null? code) '())
    (else
     (cons (list (instruction-addr (car code))
                 (instruction-op (car code))
                 (instruction-dest1 (car code))
                 (instruction-dest2 (car code)))
           (listing (cdr code))))))

(define (interpret program data)
  (define (helper program data pc)
    (cond
      ((null? program)
       (list "terminate at" pc))
      ((null? data) "out of data")
      ((> pc (instruction-addr (car program)))
       (helper (cdr program) (cdr data) pc))
      ((eq? (car data) 'D)
       (display "At state ")
       (displayln pc)
       "Die")
      (else
       (display "At state ")
       (displayln pc)
       (helper (cdr program)
               (cdr data)
               (if (eq? (instruction-op (car program)) 'brT)
                   (if (eq? (car data) 'T)
                       (instruction-dest1 (car program))
                       
                       (+ 1 pc))
                   
                   (if (eq? (car data) 'F) ; must be a brF
                       (instruction-dest2 (car program))
                       (+ 1 pc)))))))
  (displayln data)
  (helper program data 0))

(define (sc exp data)
  (displayln exp)
  (let ((code (compile exp)))
    (displayln (listing code))
    (interpret code data)))

(define (scLuser exp data)
  (displayln exp)
  (cond
    ((not (exp? exp)) "Not an expression")
    ((not (= (operandCount exp) (length data))) "Bad T/F/D list")
    (else
     (let ((code (compile exp)))
       (displayln (listing code))
       (interpret code data)))))

 (sc '(if x x x) '(T F T))
 (sc '(if (and x x) (or x x) (and x x)) '(T T T T T T))