
;----------------------------------------------------------------------------------------------------
;1.3
;------------------------------------------------------------------------------------------------------

;; 1.3 After giving a specification for the environment subsystem of TLS, prove that your implementation
;;     satisfies this specification.  Then change the representation of environemnts to use lists of
;;     bindings rather than the names-values pairs shown in the text, and show that the altered
;;     representation both satisfies your specification and works with the rest of the interpreter.


;------------------------------------------------------------------------------------------------
;Specs of the  current Enviorment
;----------------------------------------------------------------------------------------------------

;The Reprsentation Language

;1.Each Entry has two lists of equal length;
    ;names =(n, n+1,....n+......)
    ;values=(v, v+1 ......v+.....)
; provided this we can say that n1 and vs are binded via having the same index

;2. a table is a non-empty or empty list whose elements are entries. the most recent entry
;is the innermost scope

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;empty-env: ()
;Produces an empty environment
;Returns a value that satifies the Table reprsentation and contains no bindings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;build: bulid takes in two lists, being name and value lists and returns an entry
;Pre; Let s1 be a list of names
; s2 be a list of values
;the length of S1 and S2 must be equal

;Post: Returns an entry whos first element is s1 and second is s2
;In the format of (s1.s2)

;defined as

;(define build
;  (lambda (s1 s2)
    ;(cons s1 (cons s2 '()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;extend-table: takes in two lists and a table and returns a table

;Pre:
;takes formals which is a list of symbols whos length is equal to the length of vals
;vals is a list of values
;Table satisfies Reprsentation 2

;Post
;returns (cons(build formals vals) table)

;Build tells us the new head is a valid entry so the whole result satisfies the Table representation

;Defined by:
;(define (extend-table formals vals table)
 ; (cons (build formals vals) table))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;lookup-in-entry: takes in a name and entry and a error funcition and returns a value or the error function
;Purpose: to search for a frame
;Pre: name=symbol
;entry satisfies the 1st represntation described above
;entry-f is a procedure that runs when there is a failure

;Post
;if the name appears at the postion [i] in the names list, return the [i] element of the values list
;else tail reccurses until the names list is null and then evaluaturs the entry-f function

;defined by:
;
;(define (lookup-in-entry name entry entry-f)
 ; (let loop ((names  (first  entry))
           ;  (values (second entry)))
    ;(cond ((null? names)           (entry-f name))
        ;  ((eq? (car names) name)  (car  values))
         ; (else                    (loop (cdr names) (cdr values))))))










;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;lookup-in-table- takes a name and table and an error function and returns either the value or an error message
;Purpose:This is a lexically scoped lookup
;Pre:
;Table satisifes the Table represnetation
;table-f is a failure messahe

;Post:
;Searches from left to right
;Returns the value bound to the first occurance of the name given;
;if no binding is found we evaluate(table-f name)


;defined as:
;(define (lookup-in-table name table table-f)
 ; (cond ((null? table)
        ; (table-f name))
       ; (else
         ;(lookup-in-entry name (car table)
                          ;(lambda (name)
                           ; (lookup-in-table name (cdr table) table-f))))




;-----------------------------------------------------------------------------------------------
;Proofs as defined from 1.1
;----------------------------------------------------------------------------------------------

;empty-env
;Pre condtion: none since
;Post condtion: returns '()

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;build
;Precondtion: names is a list of unique symbols which has the same len as values
;Post condtion: returns a pair of (names.values)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;extend-table
;;Since this line of code has no recursion we will use proof by construction:

;:Proof:
;(build formals vals) -> this create a proper entry,
;the cons prepends this entry to an existing table
; Therefore extend-table correctly implements environment extension by proof of construction.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Lookup-in-entry

;Proof:

;pre: takes three arguments. name (the symbol to look up), entry(a list where we essentially do the searching), entry-f(error message).
;post: if name is found in the list, it returns the corresponding value. if not found, it returns the error message.
;Base Case: When names list is empty, call the function entry-f
;IH: Assume (lookup-in-entry name (cdr entry) entry-f) works correctly for smaller lists

;IS: If (car names) matches the target: it will return (car values) 
; if this is not the case then the recursion step will commence. Recurs on (cdr names) and (cdr values)
;By IH, this will either find the name or call entry-f
;Therefore, lookup-in-entry correctly searches through name-value pairs.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;lookup-in-table
;precondition:table is a list of entries
;Postcondtion: searces each entry using lookup-in-entry, else it calls table-f

;This is the proof for lookup-in-table
;For this proof, we will use structural induction

;Proof:
;Base Case:when tables is null, call the function table-f

;IH: Assume (lookup-in-table name (cdr table) table-f) works correctly and returns the value bound to name

;IS: the procedure first Tries (lookup-in-entry) on (car table)
;If the name is in that frame than the returned value is correct and we stop looking
;If we fail to find a correct value in the current frame then we do a reccursive call on the cdr of the table
;Accoring to our IH and previous steps the reccursive value will give us the corrrect lexical binding,
;at every step if we dont fuffill the IH we keep reccursing on (cdr table) until we fufill our IH or we hit
;our base case.

;Therefore, lookup-in-table works correctly.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;-----------------------------------------------------------------------------------------------
;name, value pairs ->>>>>> List-of-Bindings
;-----------------------------------------------------------------------------------------------


;changing the representation of environemnts to use lists of bindings rather than the names-values pairs
;SO far our implementation consists of name value pairs in the enviorment tables,
; previously our enviorment tables :
;(( x y z)( 1 2 3))

;We want to change that into

;((x.1)(y.2)(z.3))



;In order to do this we would have to implement some of the enviorment attributes
;that we learned about in eopl.

;In eopl there are 4 important function enviormiorments
;We have empty-env,extend-env,extend-env*, and apply env

;------------------------------------------------------------------------------------------------
;The New Enviorment
;------------------------------------------------------------------------------------------------
;( define empty-env '())
;Post condtion: Returns an enviroment with zero bindigns

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;(define (extend-env name val env) 
  ;(cons (list name val) env))

;Pre condtion: name is a symbole and env satisfies representation invarient

;Post:Returns an envirinment whos binding is (name.val) and has a tail of env

;Base case: If names is null then vals should also be null so program returns the env

;Inductive hypothesis: Assume that for the lists rest-names and rest-vals,the enviorment correctly
;extends for all other bindings from rest-names to rest-vals

;Inductive step:we let our names be (cons name rest-names) and our values be (cons val rest-vals)
;this will result in our extend*env looking like extend*env rest-names rest-vals(extend-env name val env)
;Via the defention of our IH our extend*env should add all the bindings from rest-names and rest-vals
;Via the proof from extend-env our env(car names)(car vals) should be added to the front.
;Therfore the full call builds and enviorment with the bindings from names and vals.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(define (extend-env* names vals env)
 ; (if (null? names)
     ; env
     ; (extend-env* (cdr names)
                  ; (cdr vals)
                  ; (extend-env (car names) (car vals) env))))

;Structural Indcution on names

;Pre-condition: names and vals must be lists of an equal length.

;Post condtion: Returns an environment whose left-to-right sequence of bindinfs is exactly the name/vals pairs
;followed by the original env

;Base case: names='() returns env because there are no more bindings to add

;Inductive hypothesis:Assume the reccursive call with (cdr names) and (cdr vals) correctly extends env with tail bindings

;Inductive step: our extend-env prepends the binding for (car names) and (car vals) which produces
;a new environment env. Since we proved that exten-env is correct we can say that the env satsisfies
; the invarient and adds the exact binding providied.
;Via the IH our reccursive call extends env with the other bindings to fufill the name vals pair.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;(define(apply-env env name)
;  (cond ((null? env)
       ;  (error 'apply env(format "unbound identifier: ~a" name))) 
       ; ((eq? name (car(car env)))
       ;  (cadr(car env)))
       ; (else
       ;  (apply-env(cdr env) name))))


;Inducting Structurally on env

;Pre-Condtion: env satisfies the invarient and name is a symbol
;Post-Condtion:returns the value bound to the leftmost occurance of name, if it does not find it
;it signals unbound identifier


;Base Case: (env='()) this triggers the error and it tells us that the name is unbound.

;Inductive Hypothesis: Assume (apply-env(cdr env) name) returns the innermost binding of name or signals
;the unbound error

;Inductive Step:If the name and the (car(car env)) holds true then the correct value is the (cadar env)
;which is returned immediately
;if the first condtion is not true the procedure reccurs using (cd env) By our IH this results in the correct
;result for the remaining bindings since each step would hit one of the two condtions until we return the (cadar env)
;or the base case is executed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;-------------------------------------------------------------------------------------------------
;Transforming the rest of the code for compatibility
;------------------------------------------------------------------------------------------------

;Since we defined a new enviorment we have to change some of the functions in order to ensure compatibility
; Old version used:
; (define (extend-table formals vals table)
;   (cons (build formals vals) table))

;New version:
;(define (extend-table formals vals table)
 ; (extend-env* formals vals table))

;Old version used
; (define (*identifier e table)
;   (lookup-in-table e table initial-table))

;New Version:
;(define (*identifier e table)
  ;(apply-env table e))


;--------------------------------------------------------------------------------------------
;Spec analyzation
;--------------------------------------------------------------------------------------------
;1.3 also asks us to show that our newly defineed enviorment fufills the previous specs we defined
;;The key functions in the Current TLS are:
;-empty-env: returns an empty table ()
;-build : constructs an entry from a  list of names and a list of values
;-extend-table: preappends a new entry to the enviorment
;-lookup in entry: searches for a name in a single entry
;lookup-in-table:reccursivly searchs throigh the table for a binding

;empty-env: ()
;Returns a value hat satifies the Table invarient and contains no bindings:
;extend-table: takes in two lists and a table and returns a table.
;lookup-in-entry: takes in a name and entry and a error funcition and returns a value or the error function.
;lookup-in-table- takes a name and table and an error

;In our new enviorment
;-empty-env stays as empty-env
;-build is replaced by extend env where extend env takes a name value pair and puts it in front
;-extend-table is replaced by extend-env* which preappaneds a new entry to the enviorment
;-lookup-in-entry-lookup-in-table is replaced by apply which uses reccursion and as proved fufils both the singel and reccursive binding of looking up in a enviorment and table



;------------------------------------------------------------------------------------------------
;Overall analysis and conclusion
;-----------------------------------------------------------------------------------------------

;How did alterning our lookup enviorment and enviorment in general ensure that our enviorments represent list bindings?

;Initally with our pure TLS translation our entry was two parallel lists with a name and value relatshonship.
;Lookup table would grab an entry then would find the postion of the name and return the matching value.
;  our  initial table consisted of a list of entries which relied on two diffrent lists.

;After the implementation of a new enviorment our program followed the binding model which eliminates
; the need for the name value relatshonship making the table a list of bindings
;This required all our identifiers to go through apply-env which susbstituted for lookup-in-entry and lookup-in-table.
;Once that is updated we then had to change extend-table to match our new enviorment and that required the use of extend-env* which
;instead of forming a name value pair, it pushed bindings for every actual pair so instead of (x y z)( 1 2 3) extend-env* would
;do ( x 1), ( y 2), ( z 3)


;showing that the altered
;;representation both satisfies your specification and works with the rest of the interpreter.

;The same empty env shown above
( define empty-env '())

;the same extend-env shown above
(define (extend-env name val env) 
  (cons (list name val) env))

;the same extend-env* shown above
(define (extend-env* names vals env)
  (if (null? names)
      env
      (extend-env* (cdr names)
                   (cdr vals)
                   (extend-env (car names) (car vals) env))))

;the same apply-env shown above
(define(apply-env env name)
  (cond ((null? env)
         (error 'apply env(format "unbound identifier: ~a" name))) 
        ((eq? name (car(car env)))
         (cadr(car env)))
        (else
         (apply-env(cdr env) name))))

;the changed extend-table as mentoined above
(define (extend-table formals vals table)
  (extend-env* formals vals table))





(define (atom? x)
  (and (not (pair? x)) (not (null? x))))


(define (count-elements lst)
  (if (null? lst)
      0
      (+ 1 (count-elements (cdr lst)))))



(define (add1 n)
  (+ n 1))



(define (sub1 n)
  (- n 1))


(define first car)



(define second cadr)



(define third caddr)




(define (else? x)
  (and (atom? x) (eq? x 'else)))



(define question-of first)



(define answer-of second)




(define cond-lines-of cdr)



(define function-of car)



(define arguments-of cdr)




(define text-of second)



(define table-of first)



(define formals-of second)



(define body-of third)


(define (const-atom? a)
  (or (number? a)
      (eq? a #t) (eq? a #f)
      (memq a '(cons car cdr null? eq? atom? zero? add1 sub1 number?
                     + - * / < > <= >=))))



(define (extend-table formals vals table)
  (extend-env* formals vals table))


(define (meaning e table)
  ((expression-to-action e) e table))


(define (initial-table name)
  (error "Unbound identifier" name))




(define (check-set list1)
  (cond
    ((null? list1) #t)
    ((member (car list1) (cdr list1)) #f)
    (else
     (check-set (cdr list1)))))


(define (check-equal-len-list list1 list2) 
  (cond
    ((and (null? list1) (null? list2)) #t)
    ((or (null? list1) (null? list2)) #f)
    (else
     (check-equal-len-list (cdr list1) (cdr list2)))))



(define build list)
(define new-entry build)


(define (primitive? fun)
  (and (pair? fun) (eq? (first fun) 'primitive)))


(define (non-primitive? fun)
  (and (pair? fun) (eq? (first fun) 'non-primitive)))



(define (*const e table)
   (cond
     ((number? e) e)
     ((eq? e #t) #t)
     ((eq? e #f)#f)
     (else
      (build 'primitive e))))



(define (*quote e table)
  (text-of e))


;the changed *identifier as described above
(define (*identifier e table)
  (apply-env table e) )     



(define (*lambda e table)
  (build 'non-primitive (cons table (cdr e)))) 



(define (evcon lines table)
  (cond
    ((else? (question-of (car lines))) (meaning (answer-of (car lines)) table))
    ((meaning (question-of (car lines)) table)
     (meaning (answer-of (car lines)) table))
    (else
     (evcon (cdr lines) table))))




(define (*cond e table)
  (evcon (cond-lines-of e) table))



(define (evlis args table)
  (if (null? args)
      '()
      (cons (meaning (car args) table) (evlis (cdr args) table))))

(define (tls-apply fun vals)
  (cond
    ((primitive? fun) (tls-apply-primitive (second fun) vals))
    ((non-primitive? fun) (tls-apply-closure (second fun) vals))
    (else
     (error "tls-apply: not a function" fun))))


(define (*application e table)
  (tls-apply (meaning (function-of e) table)
         (evlis (arguments-of e) table)))    


(define (tls-apply-primitive name vals)
  (cond
    ((eq? name '+) (apply + vals))
    ((eq? name '-) (apply - vals))           
    ((eq? name '*) (apply * vals))          
    ((eq? name '/) (apply / vals))           
    ((eq? name '<) (apply < vals))           
    ((eq? name '>) (apply > vals))           
    ((eq? name '<=) (apply <= vals))         
    ((eq? name '>=) (apply >= vals))        
    ((eq? name 'cons)  (cons  (first vals) (second vals)))
    ((eq? name 'car)   (car   (first vals)))
    ((eq? name 'cdr)   (cdr   (first vals)))
    ((eq? name 'null?) (null? (first vals)))
    ((eq? name 'eq?)   (eq?   (first vals) (second vals)))
    ((eq? name 'atom?) (atom? (first vals)))
    ((eq? name 'zero?) (zero? (first vals)))
    ((eq? name 'add1)  (+ (first vals) 1))
    ((eq? name 'sub1)  (- (first vals) 1))
    ((eq? name 'number?) (number? (first vals)))
    (else (error "unknown primitive" name))))


(define :atom?
  (lambda (x)
    (cond
     ((atom? x) #t)
     ((null? x) #f)
     ((eq? (car x) 'primitive) #t)
     ((eq? (car x) 'non-primitive) #t)
     (else #f))))


(define (tls-apply-closure closure vals)
  (let*
      ((saved (first closure))
       (formals (second closure))
       (body (third  closure))
       (new-env (extend-table formals vals saved)))
    (meaning body new-env)))
  



(define (atom-to-action e)
  (cond
    ((const-atom? e) *const)
    (else *identifier)))





(define (list-to-action e)
  (cond
    ((atom? (car e))
     (cond
       ((eq? (car e) 'quote)  *quote)
       ((eq? (car e) 'lambda) *lambda)
       ((eq? (car e) 'cond)   *cond)
       (else *application)))
    (else *application)))


(define (expression-to-action e)
  (if (atom? e)
      (atom-to-action e)
      (list-to-action e)))

(define (set-f)
  (begin
    (display "Error: Not a set, duplicate elements found.")
    (newline)
    #f))



(define (entry-f name)
   (begin
     (display "Error:")
     (display name)
     (display "not in values.")
      (newline)#f))



(define(table-f name)
   (begin
      (display "Error:")
      (display name)
      (display "Not found in the table")
      (newline)#f))



(define(eq-list-f)
   (begin
        (display "Error: Lists are not of equal length.")
        (newline)
        #f))

(define (value e)
  (meaning e '()))


;List of bindings Tests by displaying enviorment:




;TEST CASES  From 1.1 showing that the new enviorment works with our interpeter 
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


;;;;NEW TESTS;;;;;;;;;;;;;;;;;;
(value '((lambda (x) x) 5)) ;->5

;nested function
(value '(((lambda (a)
            (lambda (b)
              (cons a b)))
          10)
         20))
;-> (10.20)


;Outer scoping Application
(value '(((lambda (a)
            (lambda (b)
              (cons b a)))
          7)
         8))



(define e0 empty-env)                       ; ()
(define e1 (extend-table '(x y) '(1 2) e0)) ; ((x y) (1 2))
(define e2 (extend-table '(x)   '(99)  e1)) ; ((x) (99))  ((x y) (1 2))



(value '((lambda (x) (add1 x)) 3))                    ; 4
(value '(((lambda (a) (lambda (b) (cons a b))) 10) 20)) ; (10 . 20)
(value '(((lambda (a) (lambda (b) (cons b a))) 7) 8))    ; (8 . 7)


(value '(((lambda (x) (lambda () x)) 42)))            
(value '((lambda (x) ((lambda (x) x) 99)) 5))         
(value '(cond ((null? '()) 'empty) (else 'never)))

(define e1
  (extend-env 'x 10 e0))

(apply-env e1 'x)

(define e2
  (extend-env* '(y z) '(20 30) e1)) ; → ((y 20) (z 30) (x 10))

(apply-env e2 'x) ; → 10
(apply-env e2 'y) ; → 20
(apply-env e2 'z) ; → 30

;Lexical scoping example
(define e3
  (extend-env 'x 999 e2))
;here our e2 x refers to 10 however the output would be 999 since its most recently binded

  (apply-env e3 'x)

(apply-env e3 'y)




