; This is for section 1.5 of the project

;; ==================================================================================================
;1.5 After carefully identifying a standard of correctness, prove that your implementation of TLS is
;correct according to that standard.
;; ==================================================================================================


;;; Standard of Correctness:
;;; The TLS interpreter is correct if for any s-expression sexps in the TLS subset,
;;; (evaluate sexps env) returns the same value that a standard R5RS Scheme
;;; interpreter would return for sexps in an environment with equivalent bindings.


;; TLS s-expressions can be:
;;   - Constants: numbers, booleans
;;   - Symbols: variables
;;   - Quoted expressions
;;   - Lambda expressions
;;   - Conditionals (cond), (if), (else)
;;   - Function applications


(define (meaning e table)
  ((expression-to-action e) e table))

#|
So let's start off with the base case of the interpreter.
We can say constants and symbols are the base case since they are not built from smaller TLS expression.
While lambda, cond, and functions are built of s-expressions. 


=============================================
Base Cases
=============================================

Base case 1: e is a constant (number or boolean),
Base case 2: e is a variable (symbol)



==========================================
Inductive Hypothesis
==========================================

Assume that for all s-expressions e1, e2..., ek of expression e
(meaning ei table) =[ei]table for i = 1 ..., k

=========================================
Inductive Step
=========================================

;;come back to this
;; need to use cond, lambda, etc.



|#
