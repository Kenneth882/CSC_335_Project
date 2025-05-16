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
; our findings and research of lexical scope, along the way we decided
;to do a comparison between Dynamic and Lexical scoping.



;Dynamic scoping is looked at like a  stack like structure where the varible pushed is whats first in the scope/ innermost function.
;So the most recent binding varible is what is used even if the varible was defined in a diffrent scope.
;So the most recent varible determines the value of it at run time regardless of where the function was originally defined.

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
; of where the function is defined.

;A closures enviorment consists of the set of varible bindings that were in the scope
;at the place where the lambda function is set, so the function not only remembers
; the names of the varibles but al the location of the names refered to in the environment.



;; This means that even if the function is passed around or invoked in a completely different context, 
;it will still have access to the variables it closed over at the time of its creation.

; For example, if a function uses a variable `x` and is defined inside an environment where `x = 5`,
; the closure will preserve that binding of `x` no matter where or when the function is later called.





; ------------------------------------------------------------------------------
   ; TLS Implementation of Lexical Scope and Closures
; ------------------------------------------------------------------------------

;A lambda expression is converted into a closure by capturing the current enviorment.
;Capuring the enviorment means that we save the current varible bindings when the function
;is defined so we can use it for later.
;Our TLS uses enviorment capturing and closures to show lexical scoping.


;(define (*lambda e table)
 ; (build 'non-primitive (cons table (cdr e))))

;How does this function show Lexical Scope and Closures???
;for the function listed above the most important parts consist of table and the cdr e
;The table shows that the enviorment that exists where the lambda is defined and not actually
;where its later called

;This gives us lexical scope because every free varible that appears in the body is looked-up
;in this current saved enviorment which fuffils lexical scoping since lexical scope
;refers to the location.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;(define (tls-apply-closure closure vals)
  ;(let*
      ;((saved (first closure))
      ; (formals (second closure))
       ;(body (third  closure))
       ;(new-env (extend-table formals vals saved)))
  ;  (meaning body new-env)))

;How does this function show Lexical scope and Closures??
;In our tls-apply-closure our saved is the enviorment that is captured from *lambda
;the extend-table pushes a newe frame that binds each formal to its corresponding
;argument vals
;When the meaning evaluates the bdoy any parameter lookup will find the binding in the most
;receent frame, and any free varible will then fall through the frame and will be found in the
;scope where it was defined showing lexical scope.



;(define (*identifier e table) 
;  (apply-env table e) )

;How does this function show lexical scope and closures??
;our *identifer enforces lexical scoping by checking gof thr value when the closure wad created,
;if the frame has no name then we get the unbound-identifier error.


;(extend-table formals vals saved-env)
;How does this function show lexical scope and closures??
;The extend function is an important part to lexical scoping in our TLS. It takes a set of parameters
;being named formals and corresponding arguments vals, and extends the captured enviorment table with
;its new bindings.This is important because it is refered to in our tls-apply-closure which
;applies a lambda by evaluating its body in a new environment.
;The saved-env is the environment that was captured at the function defenition.Since we are
;then extending the environment, extend0table ensures the functions have acess to the bindings
;that were in the scope when they were defined and not called, showiing lexical scoping.



; These code snippits demonstrate lexical scoping:
; - When a lambda is created, the current table is captured into the closure.
; - When called, a new environment is built over the saved table.
; - Variable lookup always uses the environment stored in the closure.


; ------------------------------------------------------------------------------
;  Structural Induction Argument for Correctness
; ------------------------------------------------------------------------------

;This will be an induction on our TLS showing the satisfaction of Lexical scoping

;What we are tyring to prove:
;For every closed Tls expression e, evaluation of e by our interpreter obeys lexical-scope rules

;Base case:The base case conssits of a single varible lookup where a varible is looked up by using apply-env
;apply-env checks the first fram of the current environment and if the name is not there
;it keeps going through the list
;the current environemnt lsit always reprsents the place of where the code was written
;So for single varible lookup the value found is the correct one.

;Inductive Hypothesis
;for any s in the current code, where s is a shorter e, we run s and every varible in our s
; will be found in the correct lexical scope


;Inductive step: given a function containg lambda, when our interpeter see the lambda it makes a closure
;consisting of (saved-env formals vody)
;saved-env is the list of varible frames that exists currently which is packed inside the closure
;once our arguments are evaluted we call the tls-apply-closure which builds a new environment
;consisting of a frame with parameters as well as the saved env which is the same list
;as when the lambda function was made.
;After we make the environment, every varible inside the body is looked up with the apply-env funtion
;if out parameer comes from an outside varible we look through our saved-env which will return the
;exact location giving us the correct value.. Then via our IH every smaller expression inside of the bdoy
;also looks uo the correct names in the saved-env.

;So therfore because our Base case works and we have proved our Inductive step and how it
;relates to out Inductive Hypothesis we can say that for every s, our e will also work for
;all tls programs showing how our TLS follows lexical scoping.



