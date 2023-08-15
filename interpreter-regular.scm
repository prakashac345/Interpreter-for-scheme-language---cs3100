(load "recscm.scm")
(load "records.scm")
(load "tree.scm")
;A partial implementation of the interpreter discussed in the class
;Covers identifier, true/false, plusExpr and IfExpr

(define empty-env
  (lambda () '()))

(define extend-env
  (lambda (id val env)
    (cons (cons id (make-cell val)) env) 
    ))

(define update-env
  (lambda (id val env)
    (record-case env
                 (normal-env (ids vals env)
                             (cond ((empty? env) (update-env id val (cdr env)))
                                   ((equal? id (caar env)) (set-cell! (cdar env) val))
                                   (else (update-env id val (cdr env)))))
                 (rec-env (recdecl-list old-env)
                          (cond ((empty? old-env) (update-env id val (cdr env)))
                                ((equal? id (caar old-env)) (set-cell! (cdar old-env) val))
                                (else (update-env id val (cdr old-env)))))
                 (else (if (equal? id (caar env)) (set-cell! (cdar env) val) (update-env id val (cdr env)))))))

(define apply-envn
  (lambda (env id)
    (if (or (null? env) (null? id))
        null
        (let ((key (cadaar env))
              (val (deref-cell (cdar env)))
              (env-prime (cdr env)))
          (if (equal? id key) val (apply-env env-prime id))))))

(define deref-cell mcdr)
(define set-cell! set-mcdr!)

(define get-proc-expr (lambda (list) (cdr (cdddar list))))

(define get-formals (lambda (list) (car list)))

(define get-body (lambda (list)
                   (caddr list)
                   ))

(define checkmember (lambda (x l) (cond ((empty? l) #f)
                                        ((equal? x (cadar l)) #t)
                                        (else (checkmember x (cdr l))))))

(define make-cell
  (lambda (value)
    (mcons '*cell value)))

(define get-decl (lambda (id list) (cond ((empty? list) '())
                                         ((equal? id (cadr (caddar list))) (cdddar list))
                                         (else (get-decl id (cdr list))))))
(define apply-env
  (lambda (env id)
    (record-case env
                 (normal-env (ids vals env)
                              (apply-envn env id))
                 (rec-env (recdecl-list old-env)
                          (let ((id-list (get-ids recdecl-list)))
                           (if (checkmember id id-list)
                               (let* (
                                       (RecProc (get-decl id recdecl-list))
                                       (ProcExpr (get-proc-expr RecProc))
                                    )
                                  (make-cell (make-closure ;; a cell
                                              (get-formals ProcExpr)
                                             (get-body ProcExpr) env)))
                                (apply-env old-env id)
                                )
                            
                 ))
                 (else (apply-envn env id))
                 )))

(define extend-env-list
  (lambda (ids vals env)
    (if (null? ids)
        env
        (extend-env-list
         (cdr ids)
         (cdr vals)
         (extend-env (car ids) (car vals) env)))))

(define get (lambda (ll) ll ))

(define get-ids (lambda (ll)
                  (letrec ((geti
                            (lambda (ll l)
                              (if(empty? ll) l
                                 (geti (cdr ll) (cons (caddar ll) l))))))
                    (geti ll '()))))

(define get-exps (lambda (ll) (letrec ((geti
                                        (lambda (ll l)
                                          (if (empty? ll) l
                                              (geti (cdr ll) (cons (car (cdddar ll)) l))))))
                                (geti ll '()))))

(define eval-Expression
	(lambda (Expression env) 
		(record-case Expression (IntegerLiteral (Token) 
			(string->number Token))
		(TrueLiteral (Token) #t)
		(FalseLiteral (Token) #f)
		(PlusExpression (Token1 Token2 Expression1 Expression2 Token3)
			(+ (eval-Expression Expression1 env) (eval-Expression Expression2 env)))
		(IfExpression (Token1 Token2 Expression1 Expression2 Expression3 Token3)
			(if (eval-Expression Expression1 env) (eval-Expression Expression2 env) (eval-Expression Expression3 env)))
                (Assignment (Token1 Token2 List Expression Token3)
                            (let
                                ((id List)
                                 (vals (eval-Expression Expression env)))
                                 (update-env id vals env)
                                 )
                              )
                (Identifier (Token) (apply-env env Token))
                (ProcedureExp (Token1 Token2 Token3
                                      List Token4 Expression Token5)
                              (make-cell (make-closure List Expression env)))
                (LetExpression (Token1 Token2 Token3
                                       List Token4 Expression Token5)
                               (let* (
                                      (ids (get-ids List))
                                      (exps (get-exps List))
                                      (vals (map (lambda (Expression)
                                                  (eval-Expression Expression env))
                                                exps))
                                      (new-env (extend-env-list ids vals env))
                                      (new-normal-env (make-normal-env ids vals new-env))
                                      )
                                  (eval-Expression Expression new-normal-env)
                                 ))
                (Application (Token1 Expression List Token2)
                             (let*
                                 (
                                  (clos (deref-cell (eval-Expression Expression env)))
                                  (ids (closure->formals clos))
                                  (vals (map (lambda (Exp) (eval-Expression Exp env)) List))
                                  (static-env (closure->env clos))
                                  (new-env (extend-env-list ids vals static-env))
                                  (new-normal-env (make-normal-env (closure->formals clos) (closure->body clos) new-env))
                                  (body (closure->body clos))
                                  )
                               (eval-Expression body new-normal-env)
                               ))
                (RecExpression (Token1 Token2 Token3
                                       List Token4 Expression Token5)
                               (eval-Expression Expression (make-rec-env List env))
                               )
		(else (error 'eval-Expression "Expression not found")))))

(define run
(lambda ()
	(record-case root
		(Goal (Expression Token)
		  (eval-Expression Expression (empty-env)))
		 (else (error 'run "Goal not found")))))
(run)
