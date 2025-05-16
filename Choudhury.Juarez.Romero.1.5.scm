;; ==================================================================================================
;1.5 After carefully identifying a standard of correctness, prove that your implementation of TLS is
;correct according to that standard.

;; 1.5 Prove TLS is Correct
;; - Define what "correct" means for your interpreter.
;;     (e.g., For every valid expression e, (value e) yields the intended result.)
;; - Formally prove that your interpreter implementation satisfies this
;;   definition of correctness.
;; ==================================================================================================



;; ===================================================================================================================
; Beginning with the standard of correctness, we understand it as: what it means for our interpreter to work correctly.
; This includes what it should do for a given input and proving that it behaves as expected.
; We essentially need to prove our work by using structural induction. So we define our standard of correctness, use structural induction,
; using function code from the interpreter, and using it to make test cases. I believe that if we have all this, we have met and satisfied
; the requirements for section 1.5.
;; ===================================================================================================================




;; ===================================================================================================================
;;STANDARD OF CORRECTNESS FOR OUR TLS INTERPRETER:
#|
Our TLS interpreter is correct if, for every valid TLS expression, it produces the same result as R5RS Scheme, where the expression is within the subset of
Scheme supported by The Little Schemer (TLS). That means our interpreter should evaluate expressions in the same way as an R5RS interpreter, assuming
functional behavior and TLS-specific constraints. Basically semantic preservation. Further, our interpreter should also consider and do lexical scoping,
make closures properly, and evaluate expressions as well.

1) Primitive Evaluation. The primitive procedures like car, cdr, cons, atom?, etc must produce the same results as their R5RS Scheme equivalents.

2) Functions and Closures. In TLS, function definitions are represented as closures (formal parameters, a function body, and the environment). Our interpreter must ensure
that closures maintain proper bindings for parameters during the function application, and evaluates the body using lexical scoping rules thus resulting in the
correct result, no errors or anything incorrect.

3) Error Handling. The interpreter must detect invalid expressions, such as unbound variables or incorrect function applications. In TLS, they have error functions such as
entry-f, table-f, and build-f. Our implementation must ensure that such errors are correctly identified and outputted like R5RS Scheme. 

4) Conditionals.  In TLS and Scheme, conditionals such as cond, if, and else must correctly evaluate branches based on the first true condition. Our interpreter must ensure
that conditions are checked in order, and the result expression for the first true test is returned. This should be consistent with R5RS Scheme.
|#





;; ===================================================================================================================
;; PROVING THAT THE IMPLEMENTATION OF OUR TLS INTERPRETER MEETS THE STANDARD
;; ===================================================================================================================


;; ===================================================================================================================
;Let's focus on number 1, primitives. In TLS, cons, car, cdr, null, eq?, etc, etc are constants. We know this because in the atom-to-action
;function listed above, they're *const. Each primitive should be applied correctly.

;Two of the most important functions that we will need from our interpreter is meaning and value. The meaning function dispatches to the
;correct action. Next is value. Value evaluates an expression e in the initial environment. And because primitives consist of car, cdr, cons
;atom? we want to show that using *const to verify our proof further.

#|
(define (meaning e table)
  ((expression-to-action e) e table))

(define (value e)
  (meaning e '()))

(define (*const e table)
   (cond
     ((number? e) e)
     ((eq? e #t) #t)
     ((eq? e #f)#f)
     (else
      (build 'primitive e))))
|#


; (atom-to-action 'cons) ;#<procedure:*const>
; (atom-to-action 'eq?)  ;#<procedure:*const>
; (atom-to-action 'add1) ;#<procedure:*const>

; (value '(add1 9))          ;10
; (value '(sub1 8))          ;7
; (value '(number? 1))       ;#t
; (value '(number? 'a))      ;#f
; (value '(cons 'a '(b c)))  ;(a b c)
; Each result matches what we'd expect in TLS and R5RS Scheme for these primitives. This proves that our interpreter correctly recognizes
; these primitive symbols and applies them correctly. Keep in mind that for TLS, we don't have +, *, -, /, we need to make things like add1, sub1.

; Base Case: Each primitive is represented by a constant function returned from atom-to-action which maps them to *const.
; IH: Assume that for all arguments k1, k2, ..., kn passed to a primitive, each ki is evaluated correctly by TLS and gives the correct value
;     expected by R5RS.
; IS: For each primitive that we have defined, we can apply it using value and then confirm with R5RS. 
;; ===================================================================================================================





;; ===================================================================================================================
;Now let's focus on number 2, functions. In TLS, functions are represebted as lambda expressions which are interpreted as closures in TLS. A closure has
;formal parameters, the body, and the environment. *application evaluates the function and its arguments, and then applies the function
;using tls-apply. Basically lambda expressions => identified via expression-to-action => dispatched through list-to-action => to *lambda => makes the closure.
;The functions body must be evaluated in a new environment where the formal parameters are bound to the values. We need extend-table because
;that is how the new environment is created, the new one goes in front of the previous one. And lookup-in-table is needed since variables are looked up in the
;table. And then this finds the correct value.
;This ensures that functions follow the lexical scoping rules and that closures are properly made.

#|
(define (*application e table)
  (tls-apply (meaning (function-of e) table)
         (evlis (arguments-of e) table)))

(define (extend-table formals vals table)
  (cons (build formals vals) table))

(define (lookup-in-table name table table-f)
  (cond
    ((null? table) (table-f name))
    (else (lookup-in-entry name (car table)
           (lambda (name)
             (lookup-in-table name (cdr table) table-f))))))

(define (*lambda e table)
  (build 'non-primitive (cons table (cdr e))))
|#



; (value '((lambda (x) x) 1))                                ;1
; (value '((lambda (x) (add1 x)) 99))                        ;100
; (value '(((lambda (x) (lambda (y) (cons x y))) 'a) 'b))    ;(a . b)
; (value '((lambda (x y) (cons x (cons y '()))) 'a 'b))      ;(a b)
;Here lambda expressions are turned to closures, parameters are bounded, and the final values match with what R5RS Scheme would return.

; Base Case: A lambda expression and a primitive is essentially defined via expression-to-action which uses list-to-action and atom-to-action.
;            If it is a user defined lambda, it goes to list-toaction and then *lambda makes a closure (formal parameters, body, and environment)
; IH: Assume that any expressioin within the lambda body or closure environment will return the correct result as R5RS Scheme.
; IS: So in the interpreter, when the lambda is evaluated, it makes a closure. And this in the closure, the arguments are evaluated, then the
;     arguments are bounded to them, and then the body is evaluated in the environment.
;; ===================================================================================================================







;; ===================================================================================================================
;Now lets focus on errors. In TLS, some functions end in `-f`, such as entry-f, table-f, and build-f. These functions are responsible for
;returning messages like undefined variables, invalid application, or wrong numbers of arguments. The wording may not be the exact same however, it is
;used in the same instances.

#|
(define (entry-f name)
   (begin
     (display "Error:")
     (display name)
     (display "not in values.")
      (newline)#f))
|#

;(value '((lambda (x y) x) 1))  ;returns error
;(value '(car 5))               ;returns error
;(value '(5 3))                 ;returns error
;Although these messages may not be identical to R5RS errors, the conditions under which errors occur do. It's basically like entry-f is the Scheme error
;for undefined variable. build-f is the error for invalid. And ultimately, it does meet our standard of correctness.

; Base Case: : TLS defines error-handling by making functions like entry-f, build-f, and table-f to give errors like R5RS Scheme: undefined, invalid.
; IH: Assume that for any expression that results in an error in TLS it will return a similar error in R5RS.
; IS: While the exact error messages can be different from R5RS, they essentially say the same thing. And it is shown in the test cases.
;; ===================================================================================================================








;; ===================================================================================================================
;Now lets focus on conditions. In TLS and R5RS Scheme, conditionals are evaluated using cond special form. Each clause in a cond
;expression is a pair: a test expression and a result expression. The clauses are checked in order until the first one that evaluates to true
;is found and then its result is returned. Our interpreter uses *cond, which calls to the helper function evcon. The function evcon` walks through the
;clauses, checking each one with meaning and returns the value of the corresponding result expression. If no conditions match, we have the else.

#|
(define (*cond e table)
  (evcon (cond-lines-of e) table))

(define (evcon lines table)
  (cond
    ((else? (question-of (car lines)))
     (meaning (answer-of (car lines)) table))
    ((meaning (question-of (car lines)) table)
     (meaning (answer-of (car lines)) table))
    (else
     (evcon (cdr lines) table))))
|#

;(value '(cond ((#f 'hello) (#t 'world))))                ;world
;(value '(cond ((zero? 1) 'no) ((zero? 0) 'yes)))         ;yes
;(value '(cond ((number? 'x) 'lebron) (else 'hamim)))     ;hamim
;(value '(cond (else 'noclausehere)))                     ;noclausehere
;(value '(cond ((#f 'x) (#f 'y) (else 'z)))               ;z
;(value '(cond ((#f 'a))))                                ;we get an error here because there is no else clause.



;Base Cases: 1)When a cond expression only contains a single else clause the interpreter directly evaluates the expression `e` and returns that value.
;            2)If there are no clauses, then we get an error message because a) nothing to evaluate and go through and b) no else case either.

;IH: Assume that all expressions used in cond q1, q2,.. and the results a1, a2,.. are evaluated correctly by the interpreter.

;; IS
;; For a skeleton cond
#|
(cond
  (q1 a1)
  (q2 a2)
  ...
  (else an)
 )
|#

;The way this works is that it goes through each condition one by one IN ORDER. So q1 first, then q2, then q3 and so on and so forth. So if q1 is true, it returns
;a1. However, if it is false, then it goes to q2 and does the same thing (check is condition q2 is true or not) if not true, go to q3. But if true, return a2.
;And the big picture is if neither q1, q2, etc etc are not true. We go to an else clause. And whatever the else clause is, we need to return it. So we need clauses
;and we need an else clause if we are using cond. ;Because conditions are checked in order and only the first truthy is evaluated, this follows Scheme semantics and
;ensures correct behavior. This proves that conditionals in our TLS interpreter are correct.


;Based on our standard of correction and our proofs, we strongly believe that our implementation of the TLS Interpreter is correct.
