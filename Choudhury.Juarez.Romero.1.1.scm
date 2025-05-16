;Members: Alexis Juarez, Hamim Choudhury, Kenneth Romero
;TLS Project
;Professor Troeger


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Project: TLS Interpreter in R5RS Scheme
;;
;; Description:
;; This project reimplements and formally analyzes the interpreter described
;; in Chapter 10 of *The Little Schemer*. The goal is to create a minimal
;; interpreter for a small subset of Scheme using only R5RS-compliant,
;; purely functional constructs.
;;
;; In addition to the implementation, this project focuses on formal reasoning,
;; including correctness proofs, syntax validation, and comparison with
;; DrRacket's built-in interpreter.
;;
;; ============================================================================
;; 1.1 Implement TLS in pure functional R5RS, providing a full development for the code
;; including specifications for each function.  Give examples of TLS programs which work
;; with your interpreter.


;; 1.1 Implement TLS in R5RS Scheme
;; - Translate the interpreter from Chapter 10 of TLS into pure R5RS Scheme.
;; - Use only functional constructs—no mutation, macros, or side effects.
;; - Provide short specifications for each function.
;; - Include working example programs written in TLS syntax that demonstrate
;;   evaluation behavior.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; 1.1 Implement TLS in R5RS Scheme
; In chapter 10 of TLS we were introduced to an interpreter and our job is to turn it into code in R5RS.
; The first part we are introduced to in the chapter is the lookup code, which is basiclly a hashmap in other languages.
; The lookup takes in two parameters, the name you are looking for and the pair of lists, the first one which must be a set
; The lists must also be equal length



; Now how do we approach this? In chapter 10 of the book we have some functions written completely and we just need to convert that to R5RS,
; and some do not. Kenneth already began to create the basic helper functions and write the functions in Scheme (4/14/25). We started off by
; first creating the basic helper functions, the ones that are in the chapter and commonly used in TLS and then we went through the list one
; by one and made the functions. 



;===========================================================================================================
; BASIC HELPER FUNCTIONS. These are basic functions such as atom?, add1, etc.
; Or they are functions that have been translated to R5RS Scheme.
; Also included in this section are functions from TLS that we will use for our
; more complex functions, like action-to-action, action-to-list, etc.
;===========================================================================================================


; This is the atom function which will check when an element is an atom and saves us from
; using redundant code. TLS also assumes this function is built in.
;pre:  x is any Scheme value
;post: returns #t if x is an atom, else returns #f
(define (atom? x)
  (and (not (pair? x)) (not (null? x))))



;This is a simple helper function that can be called that counts the number of elements in a list
;pre: lst is a list
;post: this returns the number of elements in a list
(define (count-elements lst)
  (if (null? lst)
      0
      (+ 1 (count-elements (cdr lst)))))



;A function used to add by 1
;pre: n is a Scheme number
;post: returns the Scheme number with one added to it
(define (add1 n)
  (+ n 1))



;A function used to subtract by 1
;pre: n is any Scheme number
;post: returns the Scheme number with one subtracted for it
(define (sub1 n)
  (- n 1))





;===========================================================================================================
; This is a section of functions in TLS that are aliases.

;In TLS first is defined as car
(define first car)


;In TLS second is defined as cadr
(define second cadr)


;In TLS third is defined as caddr
(define third caddr)


;In TLS, question-of is defined as first
(define question-of first)


;In TLS, answer-of is defined as second
(define answer-of second)


;In TLS, cond-lines-of is defined as cdr
(define cond-lines-of cdr)


;In TLS, function-of is defined as car
(define function-of car)


;In TLS, arguments-of is defined as cdr
(define arguments-of cdr)


;In TLS, text-of is defined as second
(define text-of second)


;In TLS, table-of is defined as first
(define table-of first)


;In TLS, formals-of is defined as second
(define formals-of second)


;In TLS, body-of is defined as third
(define body-of third)
;===========================================================================================================

;In TLS, this is the else? function
;pre: x is any Scheme value
;post: returns #t if x is the atom else, otherwise returns #f
(define (else? x)
  (and (atom? x) (eq? x 'else)))


;===========================================================================================================
; This is the build function. It takes two arguments and makes a two element list where s1 is first and s2 is the
; second element. 
;===========================================================================================================
;;pre: takes two arguments, s1 and s2 which can be any valid Scheme values
;;post: returns a list of two elements, s1 is first and then s2 is second
(define build
  (lambda (s1 s2)
    (cons s1 (cons s2 '()))))

;Testing the function
; (build '(x y z) '(1 2 3))              ;returns ((x y z) (1 2 3))
; (build '((a . 1) (b . 2)) '((x . 9)))  ;returns (((a . 1) (b . 2)) ((x . 9)))
; (build '(a (b c)) (build '(x) '(1)))   ;returns ((a (b c)) ((x) (1)))


;In TLS, new-entry is defined as build
(define new-entry build)



;This is a custom error message that we have made.
;pre:  msg represents an error message, arg is any value providing context
;post: displays an error message followed by a newline
(define (error msg arg)
  (display "ERROR: ") (display msg) (display " ") (display arg) (newline))


;===========================================================================================================
; This is the extend-table function. What this does is extend an environment in TLS. It takes three arguments, formal parameters,
; the corresponding values, and an existing environment. It makes a new entry using build and adds it to the front of the table.
;===========================================================================================================
;pre:  takes three arguments. formals is basically a list of variable names, vals is the corresponding value for those names. table
;      is a list of entries.
;post: returns a new TLS table with the new entry in the front of the existing table
(define (extend-table formals vals table)
  (cons (build formals vals) table))

; Proof for extend-table: Since this line of code has no recursion we will use proof by construction:
; (build formals vals) makes a valid entry by binding variables to values
; the cons prepends this entry to the front of the existing table
; Therefore extend-table correctly implements environment extension by proof of construction.
;===========================================================================================================


;So this was a main reason why our code was not working. In TLS, it gives us initial-table. However, if we carefully
;read it, it says that this should never be used really. So this is just like a fall back and gives an error. 
(define (initial-table name)
  (error "Unbound identifier" name))


;===========================================================================================================
; This is the lookup-in-entry function. What this does is search for a given name (which is the symbol to look up) in
; an entry. 
;===========================================================================================================
;pre:  takes three arguments. name (the symbol to look up), entry (a list where we essentially do the searching. the first element
;      is a list of names, second is values), entry-f(error message if name is not found).
;post: if name is found in the list, it returns the corresponding value. if not found, it returns the error message.
(define (lookup-in-entry name entry entry-f)
  (let loop
    ((names (first entry))
     (values (second entry)))
    
    (cond
      ((null? names) (entry-f name))
      ((eq? (car names) name) (car values))
      (else
       (loop (cdr names) (cdr values))))))

; Testing the function
; (define entry '((x y z) (1 2 3)))
; (lookup-in-entry 'x entry (lambda (name) 'not-found-in-entry))                   ;returns 1
; (lookup-in-entry 'a entry (lambda (name) 'not-found-in-entry))                   ;returns not-found-in-entry
; (lookup-in-entry 'h2 '((h1 h2 h3) (ar luka lebron)) (lambda (name) 'not-found))  ;returns luka


; Proof by Induction
; Base Case: When (null? names) is true, then 'name' is not in the list. Thus, we get the error message.
; IH: Assume (lookup-in-entry name (cdr entry) entry-f) works correctly for smaller lists

; IS: If (car names) matches the target: it will return (car values) 
;     if this is not the case then the recursion step will commence. Recurs on (cdr names) and (cdr values)
; By IH, this will either find the name if it exists or call (entry-f name)
; Therefore, by induction, `lookup-in-entry` correctly searches through the list.



;===========================================================================================================
; This is the lookup-in-table function. What this does is search for a name in a TLS table which is a list of entries
;===========================================================================================================
;pre:  takes three arguments, name (what we are looking for), table (list of entries where each entry is a name and value pair), and
;      table-f (an error message if name is not found in any entry)
;post: returns the value associated with name if it is found in table. if it does not exist, calls the error message.
(define (lookup-in-table name table table-f)
   (cond
     ((null? table)(table-f name))
     (else
      (lookup-in-entry name (car table)
                       (lambda (name) (lookup-in-table name (cdr table) table-f))))))

;Testing the function
; (define table '(((entree dessert)
;                (spaghetti spumoni))
;               ((appetizer entree beverage)
;                (food tastes good))))

; (lookup-in-table 'entree table (lambda (name) 'not-found))    ;returns spaghetti
; (lookup-in-table 'dessert table (lambda (name) 'not-found))   ;returns spumoni
; (lookup-in-table 'appetizer table (lambda (name) 'not-found)) ;returns food
; (lookup-in-table 'snacks table (lambda (name) 'not-found))    ;returns not-found

; (define complex-table 
;   '(((alpha beta gamma)
;     (1 2 3))
;    ((delta epsilon zeta)
;     (4 5 (nested list)))
;    ((theta iota kappa)
;     ((deep nested) 8 9))))

; (lookup-in-table 'gamma complex-table (lambda (name) 'not-found))   ;returns 3
; (lookup-in-table 'zeta complex-table (lambda (name) 'not-found))    ;returns (nested list)
; (lookup-in-table 'theta complex-table (lambda (name) 'not-found))   ;returns (deep nested)
; (lookup-in-table 'lambda complex-table (lambda (name) 'not-found))  ;returns not-found


;Proof by Structural Induction
; Base Case: If (null? table) is true, then the table is empty. So thus returning the (table-f name) where name not found.
; IH: Assume (lookup-in-table name (cdr table) table-f) correctly returns the value associated with name but only if it exists,
;     else it calls (table-f name)
; IS: The function tries (lookup-in-entry) on (car table). If found, we return the correct value and done. If it is not found, we will
;     recursively go on (cdr table) By IH, this will search the remaining values correctly
;Therefore, lookup-in-table works correctly. and searches properly for name.





;===========================================================================================================
; TLS FUNCTIONS
; In TLS, it asks a crucial question, "How can we build an entry from a set of names and a list of values?"
; It then proceeds to tell us that we should try and build our examples with the function of
; (define new-entry build). And this is ultimately saying new-entry = build. So we need to make a build function.
;===========================================================================================================

;===========================================================================================================
; This is the check-set function. It checks whether or not the list has unique elements. A set cannot have any
; repeated elements (dupes).
;===========================================================================================================
;pre: list1 is a list
;post: returns #t if list1 is a set and #f if it is not a set
(define (check-set list1)
  (cond
    ((null? list1) #t)
    ((member (car list1) (cdr list1)) #f)
    (else
     (check-set (cdr list1)))))

;Testing the function
; (check-set '())                                  ;returns #t
; (check-set '(1 2 3 4))                           ;returns #t
; (check-set '((lambda (x) x) (lambda (x) x)))     ;returns #f
; (check-set '(1 2 (lambda (x) x) 3))              ;returns #t  
; (check-set '(1 2 (lambda (x) x) (lambda (y) y))) ;returns #t



;===========================================================================================================
; This is the check-equal-len-list function. It checks whether two lists are of equal length. 
;===========================================================================================================
;pre: list1 and list2 are lists
;post: returns #t or #f based on if the lists are of equal length or not
(define (check-equal-len-list list1 list2)
  (cond
    ((and (null? list1) (null? list2)) #t)
    ((or (null? list1) (null? list2)) #f)
    (else
     (check-equal-len-list (cdr list1) (cdr list2)))))

;Testing the function
; (check-equal-len-list '() '(1 2 3))                                ;returns #f
; (check-equal-len-list '() '())                                     ;returns #t
; (check-equal-len-list '(1 2 (lambda (x) x)) '(a b (lambda (y) y))) ;returns #t
          


;===========================================================================================================
; Action Functions
; In chapter 10 of TLS, we once again meet the use of value. And value is the function that returns
; the natural value of expressions. After that, we then get introduced to the different action functions
; There are different types: *const, *quote, *identifier, *lambda, *cond, and *application. And to represent
; we use action functions. We have atom-to-action, expression-to-action, and list-to-action. 
;===========================================================================================================


;===========================================================================================================
; This is the primitive? function. What this does is check if the given value is a TLS primitive procedure
;===========================================================================================================
;pre:  takes one argument. fun (can be any Scheme value)
;post: returns #t if fun is a pair whose first element is the symbol 'primitive and #f otherwise
(define (primitive? fun)
  (and (pair? fun) (eq? (first fun) 'primitive)))

;Testing the function
; (primitive? '(primitive +))                         ;returns #t
; (primitive? '(primitive car))                       ;returns #t 
; (primitive? 'primitive)                             ;returns #f     
; (primitive? '(((primitive list)) (primitive cons))) ;returns #f
; (primitive? '(((primitive /)) extra))               ;returns #f




;===========================================================================================================
; This is the non-primitive? function. What this does is check if the given value is a TLS non-primitive procedure
;===========================================================================================================
;pre:  takes one argument. fun (can be any Scheme value)
;post: returns #t if fun is a pair whose first element is the symbol 'non-primitive and #f otherwise
(define (non-primitive? fun)
  (and (pair? fun) (eq? (first fun) 'non-primitive)))

;Testing the function
; (non-primitive? '(primitive +))                         ;returns #f
; (non-primitive? '(primitive car))                       ;returns #f 
; (non-primitive? 'primitive)                             ;returns #f     
; (non-primitive? '(((primitive list)) (primitive cons))) ;returns #f
; (non-primitive? '(non-primitive (lambda (x) x)))        ;returns #t 




;Action for constants. This function handles evaluation of constant expressions.
;pre:  takes two arguments. e is a TLS expression and table is the current environment.
;post: this functions returns e if it is a number, if it is boolean, returns that boolean. else, it returns (build 'primitive e),
;      where e is a primitive procedure name.
(define (*const e table)
   (cond
     ((number? e) e)
     ((eq? e #t) #t)
     ((eq? e #f)#f)
     (else
      (build 'primitive e))))

;Testing the function
; (*const 12 'testcase)                ;returns 12
; (*const 'cons 'testcase)             ;returns (primitive cons)
; (*const '(lambda (x) x) 'testcase)   ;returns (lambda (x) x))



;Action for quote. This function just extracts the content of a quoted expression.
;pre:  this takes two arguments. e is a TLS quoted expression and table is the current environment.
;post: it returns the quoted content, and in TLS, that is the second element of e. refer to text-of at the top of file if confused.
(define (*quote e table)
  (text-of e))

;Testing the function
; (*quote '(1 2 3) 'dummy)                                   ;returns 2
; (*quote '(lambda (x) x) 'dummydata)                        ;returns (x)
; (*quote '(quote (1 2 3)) 'dummy)                           ;returns (1 2 3)
; (*quote '(quote (lambda (x) x)) 'dummy)                    ;returns (lambda (x) x)
; (*quote '(quote (lambda (x) (lambda (y) (+ x y)))) 'dummy) ;returns (lambda (x) (lambda (y) (+ x y)))
; (*quote '(quote (cond ((= x 0) 'zero) ((> x 0) 'pos) (else 'neg))) 'dummy)
;(cond ((= x 0) 'zero) ((> x 0) 'pos) (else 'neg))



;Action for identifier. This looks up the value associated with the symbol in a certain environment.
;pre:  this takes teo arguments. e is a TLS atom and table is the environment.
;post: what this does is return the value bound to e in the table. if it is not found, it returns from initial-table
(define (*identifier e table)
  (lookup-in-table e table initial-table))

;Test cases
; (*identifier 'a (extend-table '(a b) '(1 2) '()))                        ;returns 1
; (*identifier 'b (extend-table '(x) '(99) (extend-table '(b) '(42) '()))) ;returns 42
;(*identifier 'cons '()) ;ERROR: Unbound identifier cons



;Action for lambda. This makes a non-primitive procedure representation.
;pre:  this takes two arguments. e is a TLS expression and table is the current environment.
;post:  returns a list representing a non-primitive procedure in the form: (non-primitive (table params body...)) 
(define (*lambda e table)
  (build 'non-primitive (cons table (cdr e))))

; Test Cases
; (*lambda '(lambda (x) x) 'env1)                        ;(non-primitive (env1 (x) x))
; (*lambda '(lambda (x) (lambda (y) (cons x y))) 'env1)  ;(non-primitive (env1 (x) (lambda (y) (cons x y))))



;Action for cond. This evaluates the cond by going through each clause essentially.
;pre:  this takes two arguments. e is a TLS expression and table is the current environment.
;post: this evaluates each clause in the table, if one is true, the value there is evaluated and returned. if we see else, then
;      thats answer is always evaluated and returned.
(define (*cond e table)
  (evcon (cond-lines-of e) table))



;Action for application. This applies a function to a list of evaluated arguments.
;pre:  this takes two arguments. e is a TLS application (f arg1 arg2 ...) and table is the current environment
;post: this first evaluates the function by using meaning. then it evaluates the arguments by using evlist. it applies the function
;      to the argument by using tls-apply. and then it returns the result of the function application. 
(define (*application e table)
  (tls-apply (meaning (function-of e) table)
         (evlis (arguments-of e) table)))



;===========================================================================================================
; This is the atom-to-action function. This was already given to us in TLS chapter 10. The purpose of this is
; to decide how to evaluate an atomic expression. And returns the correct "action". 
;===========================================================================================================
; pre: e is any Scheme value.
; post: returns *const if e is a constant atom. else returns *identifier.
(define atom-to-action
  (lambda (e)
    (cond
      ((number? e) *const)
      ((eq? e #t) *const)
      ((eq? e #f) *const)
      ((eq? e (quote cons)) *const)
      ((eq? e (quote car)) *const)
      ((eq? e (quote cdr)) *const)
      ((eq? e (quote null?)) *const)
      ((eq? e (quote eq?)) *const)
      ((eq? e (quote atom?)) *const)
      ((eq? e (quote zero?)) *const)
      ((eq? e (quote add1)) *const)
      ((eq? e (quote sub1)) *const)
      ((eq? e (quote number?)) *const)
      (else *identifier))))

;Testing the function
; (atom-to-action 5)                                   ;#<procedure:*const>
; (atom-to-action 'list)                               ;#<procedure:*identifier>
; (atom-to-action 'lambda)                             ;#<procedure:*identifier>
; (atom-to-action '(lambda (x) (lambda (y) (+ x y))))  ;#<procedure:*identifier>
; (atom-to-action 'cdr)                                ;#<procedure:*const>
(newline)




;===========================================================================================================
; This is the list-to-action function. This was also given in TLS. The purpose of this is to handle expressions
; that are not atoms, hence why we have quote, lambda, and cond as a comparison for our eq? and return it.
; Also deals with *application. 
;===========================================================================================================
; pre: e is a non-empty list.
; post: returns *quote if (car e) is 'quote, *lambda if 'lambda, *cond if 'cond, else it returns *application.
(define (list-to-action e)
  (cond
    ((atom? (car e))
     (cond
       ((eq? (car e) 'quote)  *quote)
       ((eq? (car e) 'lambda) *lambda)
       ((eq? (car e) 'cond)   *cond)
       (else *application)))
    (else *application)))

;Testing the function
; (list-to-action '(lambda (x) ((lambda (y) (+ x y)) 5)))               ;#<procedure:*lambda>
; (list-to-action '(lambda (x) (lambda (y) (lambda (z) (+ x y z)))))    ;#<procedure:*lambda>
; (list-to-action '((lambda (x) ((lambda (y) (* x y)) 2)) 3))           ;#<procedure:*application>
; (list-to-action '((lambda (x) (lambda (y) (x y))) (lambda (z) z)))    ;#<procedure:*application>
; (list-to-action '(cond ((> x 0) x) ((< x 0) (- x)) (else 0)))         ;#<procedure:*cond>
(newline)



;===========================================================================================================
; This is the expression-to-action function. This was also given in TLS. The purpose of this can be thought of
; as the main function, it calls both of the two previous functions given what we have inputted. And then the other
; two can be considered helper functions that do all of the work. It determines how to evaluate any given TLS expression
;===========================================================================================================
; pre: e is any TLS expression
; post: returns the result of atom-to-action e if e is an atom; otherwise returns the result of list-to-action e.
(define (expression-to-action e)
  (if (atom? e)
      (atom-to-action e)
      (list-to-action e)))

;Testing the function
; (expression-to-action '(quote hello))                           ;#<procedure:*quote>
; (expression-to-action '(quote (1 2 3)))                         ;#<procedure:*quote>
; (expression-to-action '(lambda (x) (lambda (y) (+ x y))))       ;#<procedure:*lambda>
; (expression-to-action '((lambda (x) (lambda (y) (+ x y))) 3))   ;#<procedure:*application>
; (expression-to-action '(if (zero? x) 0 (add1 x)))               ;#<procedure:*application>

; ((expression-to-action '(lambda (x) (+ x 1))) '(lambda (x) (+ x 1)) '())
; (non-primitive (() (x) (+ x 1)))

; ((expression-to-action '(lambda (x) x)) '(lambda (x) x) initial-table)
; (non-primitive (#<procedure:initial-table> (x) x))

; ((expression-to-action '(lambda (x y) (+ x y))) '(lambda (x y) (+ x y)) initial-table)
; returns (non-primitive (#<procedure:initial-table> (x y) (+ x y)))

; ((expression-to-action '(lambda (x) (lambda (y) (+ x y)))) '(lambda (x) (lambda (y) (+ x y))) initial-table)
; returns (non-primitive (#<procedure:initial-table> (x) (lambda (y) (+ x y))))
(newline)
(newline)



;===========================================================================================================
; This is one of the most important functions for our interpreter. This dispatches to the correct action.

;pre: takes two arguments.  e is an expression that will be evaluated. table is the current environment
;post: returns the result of evaluating expression e in the table by using expression-to-action
(define (meaning e table)
  ((expression-to-action e) e table))
;===========================================================================================================



;===========================================================================================================
; This is another important function for our interpreter. What this does it evaluate an expression e in the initial
; environment. This is used by a lot of test cases in TLS and in class by Professor Troeger.

;pre: e is an expression that will be evaluated
;post: returns the evaluated value of e 
(define (value e)
  (meaning e '()))
;===========================================================================================================



;===========================================================================================================
; This is the evcon function. This evaluates a list of cond clauses and returns the result of the first one that satisfies.
;===========================================================================================================
;pre:  takes two arguments. lines is a list of cond clauses (each clause is a pair btw). table is the current environment
;post: if the quesion is else, it evaluates and returns the answer. if the question evaluates to true, it evaluates and returns
;      the answer. else, it goes to the next clause. 
(define (evcon lines table)
  (cond
    ((else? (question-of (car lines))) (meaning (answer-of (car lines)) table))
    ((meaning (question-of (car lines)) table)
     (meaning (answer-of (car lines)) table))
    (else
     (evcon (cdr lines) table))))



;===========================================================================================================
; This is the evlis function. It evaluates a list of expressions in the current environment.
;===========================================================================================================
;pre: takes two parameters. arguments is what needs to be evaluated. table is the current environment
;post: returns a list of the evaluated arguments in args by using meaning.
(define (evlis args table)
  (if (null? args)
      '()
      (cons (meaning (car args) table) (evlis (cdr args) table))))




;===========================================================================================================
; This is the tls-apply-primitive. What this does is apply a primitive operation to a list of argument values.
;===========================================================================================================
;pre: this takes two arguments. name (symbol representing the primitive op name). vals (a list of arguments).
;post: applies the operation and then returns the result. if it is not recognized, we return an error.
(define (tls-apply-primitive name vals)
  (cond
    ((eq? name '+) (apply + vals))
    ((eq? name 'cons) (cons (first vals) (second vals)))
    ((eq? name 'car)
     (if (null? vals)
     (error "primitive 'car' called with no arguments" name)
     (car (first vals))))
    ((eq? name 'cdr) (cdr (first vals)))
    ((eq? name 'null?) (null? (first vals)))
    ((eq? name 'eq?) (eq? (first vals) (second vals)))
    ((eq? name 'atom?) (atom? (first vals)))
    ((eq? name 'zero?) (zero? (first vals)))
    ((eq? name 'add1) (+ (first vals) 1))
    ((eq? name 'sub1) (- (first vals) 1))
    ((eq? name 'number?) (number? (first vals)))
    (else
     (error "unknown primitive" name))))

;Testing the function
; (tls-apply-primitive '+ '(1 2 3))      ;6
; (tls-apply-primitive 'cons '(1 (2 3))) ;(1 2 3)
; (tls-apply-primitive 'car '((1 2 3)))  ;1
; (tls-apply-primitive 'cdr '((1 2 3)))  ;(2 3)
; (tls-apply-primitive 'null? '(()))     ;#t
; (tls-apply-primitive 'unknown-op '(1 2)) ;error: unknown primitive unknown-op
; (tls-apply-primitive 'car '())           ;ERROR: primitive 'car' called with no arguments car
(newline)



;===========================================================================================================
; This is the :atom? function. This basically extends atom to include TLS style function representations.
;===========================================================================================================
;pre:  x is any value.
;post: rreturns $t is x is an atom, a primitive procedure, a non-primitive procedure. else it returns #f.
(define :atom?
  (lambda (x)
    (cond
     ((atom? x) #t)
     ((null? x) #f)
     ((eq? (car x) 'primitive) #t)
     ((eq? (car x) 'non-primitive) #t)
     (else #f))))

;Test cases
; (:atom? '(primitive +))                ;#t
; (:atom? '(non-primitive (env (x) x)))  ;#t
; (:atom? '(lambda (x) x))               ;#f
; (:atom? '(1 2 3))                      ;#f



;===========================================================================================================
; This is the tls-apply-closure. It applies a non primitive function to a list of argument values.
;===========================================================================================================
;pre: closure is a list with at least three elements: saved environment, formal parameters list, and body expression;
;      vals is a list of argument values that corresponds to the parameters.
;post: extends saved environment with formals bound to vals, evaluates body in the new environment, and returns the result.
(define (tls-apply-closure closure vals)
  (let*
      ((saved (first closure))
       (formals (second closure))
       (body (third  closure))
       (new-env (extend-table formals vals saved)))
    (meaning body new-env)))
  
;Test cases
; (tls-apply-closure '(() (x) x) '(42))         ;returns 42
; (tls-apply-closure '(() (a b) a) '(99 100))   ;returns 99
; (tls-apply-closure '(((x) (999)) (x) x) '(1)) ;returns 1
(newline)


;===========================================================================================================
; This is the tls-apply function. WhaT this does is dispatch application if it is a primitive or non-primitive procedure.
;===========================================================================================================
;pre: takes two arguments. fun (value expected to be prim or non-primitive procedure. vals is a list of argument values
;post: if fun is primitive, it applies tls-apply-primitive and returns. if non-primitive, applies closure and returns.
;      else error message.
(define (tls-apply fun vals)
  (cond
    ((primitive? fun) (tls-apply-primitive (cadr fun) vals))
    ((non-primitive? fun) (tls-apply-closure (cadr fun) vals))
    (else (error "tls-apply: not a function" fun))))

;Tests for function
; (define primitive-fun '(primitive +))
; (tls-apply primitive-fun '(2 3))   ;returns 5
; (tls-apply 42 '(1 2))              ;ERROR: tls-apply: not a function 42
; (tls-apply primitive-fun '(1 10))  ;returns 11








;===========================================================================================================
; Error Functions
; In chapter 10 of TLS, we get introduced to parameters within our function that ends in -f. For example, we
; have set-f, entry-f, table-f, etc, etc. These are known as error functions. Because we don't want to actually
; write an else clause and then an error message.
;===========================================================================================================
;This is an error function set-f, which returns an error message if the input is not a set.
(define (set-f)
  (begin
    (display "Error: Not a set, duplicate elements found.")
    (newline)
    #f))


;This is an error function entry-f that returns an error message if the name we are looking for/searching is
;not in the values list.
(define (entry-f name)
   (begin
     (display "Error:")
     (display name)
     (display "not in values.")
      (newline)#f))


;This is an error function table-f which returns an error message if the name we are looking for/searching is
;not in the table. 
(define(table-f name)
   (begin
      (display "Error:")
      (display name)
      (display "Not found in the table")
      (newline)#f))


;This is an error function eq-list-f which returns an error message if the two lists, are not of equal length.
(define(eq-list-f)
   (begin
        (display "Error: Lists are not of equal length.")
        (newline)
        #f))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TLS Module Dispatch (Used by Syntax Checker)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; this is our dispatch which can be called anywhere in our syntax-checker to refer to, to avoid redundancy.
;The tls-module is the function and the dispatch serves as the data value
(define (tls-module dispatch)
  (cond
    ((eq? dispatch 'primitives)
     '(car cdr cons null? pair? list? equal? atom? not
           + - * / = < > <= >= symbol? number? boolean?
           procedure? zero? add1 sub1 first second third))
    ((eq? dispatch 'special-forms)
     '(lambda cond if quote and or))
    (else (error "Unknown dispatch key:" dispatch))))
(define tls tls-module)


;===========================================================================================================
; THIS IS THE TEST CASES GIVEN BY THE PROFESSOR. DO NOT DELETE THIS OR COMMENT THESE OUT.
;===========================================================================================================

(value '((lambda (x) (add1 x)) 3))
;this returns 4


(value '((lambda (x) (add1 x))
	 ((lambda (x) (add1 x)) 4)))
;this returns 6


(value '(((lambda (y)
            (lambda (x) (cons x y)))
          3)
         4))
;this returns (4 . 3)


(value '((lambda (x z)
           (cons x
                 ((lambda (x y) (cons z x))
                  3 4)
                 ))
         1 2))
;this returns (1 2 . 3)


(value '((lambda (f y)
          (f y))
        (lambda (x) (add1 x))
        4))
;this returns 5


(value '((lambda (f y)
	   (f y))
	 ((lambda (x) (cond ((number? x) add1)
			    (else (lambda (y) (cons x y)))))
	  (quote z))
	 3))
;this returns (z . 3)


(value '((lambda (x)
             ((lambda (f)
                (cons x ((lambda (x) (f x))
                         3)))
              (lambda (y) (cons x y))))
         2))
;this returns (2 2 . 3)
