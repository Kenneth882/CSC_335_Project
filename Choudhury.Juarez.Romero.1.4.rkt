; this is 1.4 of the project



;--------------------------------------------------------------------------------------------------
;1.4 Closures and Lexical Scope in TLS
;---------------------------------------------------------------------------------------------------------
;; Question: Research closures and lexical scope, and prove that your
;; implementation of TLS supports these features correctly.
;; Provide definitions, structural insights, and use induction to justify correctness.

;----------------------------------------------------------------------------------------------------------
;Quick Backround: Lexical Vs Dynamic Scoping
;--------------------------------------------------------------------------------------------------------
;1.4 of the project is asking us to research closure and lexical scope and prove that our implementation
; of TLS implements them correctly.


;The first part of the assigment is for backround and asking us to research what exactly lexical scoping is
; our findings and research of lexical scope, along the way we decided to do a comparison between Dynamic and Lexical scoping.



;Dynamic scoping is looked at like a  stack like structure where the varible pushed is whats first in the scope/ innermost function.So the most recent binding varible
;is what is used even if the varible was defined in a diffrent scope.So the most recent varible determines the value of it at run time regardless of where
; the function was originally defined.

;Lexical scoping is when we determine the varible at compile time rather thean run time. Instead of a stack the varible
; we refer to is based on our static structure of the code.A varible is bound by the closest encolosing lambda, expression at the time the function
; is defined, not a the time it is called

;What exactly is lexical scoping?
;An items lexical scope is the place in which it was created.
;Some varibles can be delacred within a specific scope and are only accesible withing that reigon.
;Lexical Scope refers to the ability of a function scope to acess varibles from its parent scope so
; when there is a lexical scope innermost, inner and outermost functions may access all the varibles from
;their parent scopes all the way up to the global scope.
;However one key detail is that a scope cannot acess varibles from functions defined inside of it,
;so the childs function is lexically bound to the parents function.


;Basic example to show the difference between dynamic and lexical scoping

; (define y 10)
; (define (h) y)
; (define (ad) (let ((y 20)) (h)))

;In lexical scoping ad would return 10 because h was defined in an enviorment
;In dynamic scoping it would return 20 because h is called inside of the scope of y=20.


;--------------------------------------------------------------------------------------------------------
;Key concepts
;--------------------------------------------------------------------------------------------------------


;Now that we've explained the key differences between lexical and dynamic scoping we are going to go more in depth in explaining lexical scope.

;Important defenitons:

;Bound-Occurance: a bound occurance is when a varible sits inside the scope that it introduces it in.Bound has a binding right there
;Free occurance:  a varible that is not introduced locally and not bound by an local bindings. Free to look outside the local scope
;Unbound occurance: a varible that is undefined. Unbound is owned by no one.

;What is a closure?

;a closure is the run time value produced when a function is created inside some lexical enviorment, the closure will remeber the values of varibles from
; the place it is defined in and not where its called. For Lexical scoping a closure is important because it enforces that a enviorment uses the value
; of where the function is defined

;; This means that even if the function is passed around or invoked in a completely different context, 
;it will still have access to the variables it closed over at the time of its creation.

; For example, if a function uses a variable `x` and is defined inside an environment where `x = 5`,
; the closure will preserve that binding of `x` no matter where or when the function is later called.





; ------------------------------------------------------------------------------
   ; TLS Implementation of Lexical Scope and Closures
; ------------------------------------------------------------------------------

;A lambda expression is converted into a closure by capturing the current enviorment.
;
;(define (*lambda e table)
 ; (build 'non-primitive (cons table (cdr e))))


;;(define (tls-apply-closure closure vals)
  ;(let*
      ;((saved (first closure))
      ; (formals (second closure))
       ;(body (third  closure))
       ;(new-env (extend-table formals vals saved)))
  ;  (meaning body new-env)))



;(define (*identifier e table) 
;  (apply-env table e) )


; These code snippits demonstrate lexical scoping:
; - When a lambda is created, the current table is captured into the closure.
; - When called, a new environment is built over the saved table.
; - Variable lookup always uses the environment stored in the closure.


; ------------------------------------------------------------------------------
;  Structural Induction Argument for Correctness
; ------------------------------------------------------------------------------


;How does our code demonstrate that it is lexically scoped?

;From the defneition we provided above and the snipiets of code bellow is what we will use to prove that
;our implementation of TLS implements lexical scoping.

;Structure:
;Creating the lambda captures the current enviorment.
;The function applicaiton extends the captured enviorment with new bindings.
;Evaluation used the extended enviorment via 'apply' env

;Base case:
; when-Expression is a literal no lookup ocurs
;When expression is a variable, it gets evaluated using apply-env which searches the stored enviorment

;Indcutive Hyptothesis: all the subexpressions respect Lexical scoping

;When evaluating the lambda body
;- the body uses a closures enviorment and not the callers
;- Any free varibles in the body refere to the bindings in the saved or above
;Therfore all the varibles are resolved lexically based on where the function was defined in the code
; and not when its called.

;------------------------------------------------------------------------------------
;Demonstration
;------------------------------------------------------------------------------------

; This function creates a closure over x:




 ((lambda (x)
   ((lambda (f)
      ((lambda (x) (f)) 20))
    (lambda () x))) 
 10)

;Since our program is Lexicaly scoped we return 10