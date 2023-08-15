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
    (if(empty? env) (extend-env id val env)
    (record-case env
                 (normal-env (ids vals env)
                             (cond ((empty? env) (update-env id val (cdr env)))
                                   ((equal? id (caar env)) (set-cell! (cdar env) val))
                                   (else (update-env id val (cdr env)))))
                 (rec-env (recdecl-list old-env)
                          (cond ((empty? old-env) (update-env id val (cdr env)))
                                ((equal? id (caar old-env)) (set-cell! (cdar old-env) val))
                                (else (update-env id val (cdr old-env)))))
                 (else (if (equal? id (caar env)) (set-cell! (cdar env) val) (update-env id val (cdr env))))))))


(define result (lambda (l x) (if(empty? l) x (result (cdr l) (string-append (symbol->string (car l)) (string-append "->" x))))))

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
    (if (empty? env)
        null
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
                 ))))

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
                        (record-case Expression
                                     (IntegerLiteral (Token) 'Int)
                                     (TrueLiteral (Token) 'bool)
                                     (FalseLiteral (Token) 'bool)
                                     (PlusExpression (Token1 Token2 Expression1 Expression2 Token3)
                                                     (let ((type1 (eval-Expression Expression1 env)) (type2 (eval-Expression Expression2 env)))
                                                       (cond ((and (equal? type1 'Int) (equal? type2 'bool)) (error "Type Error"))
                                                             ((and (equal? type2 'Int) (equal? type1 'bool)) (error "Type Error"))
                                                             ((equal? type1 'Int) (let((t1 (update-env Expression2 'Int env)))
                                                                                    ;(extend-env Expression2 'Int env)
                                                                                    'Int
                                                                                    ;(cadr Expression2)
                                                                                    )
                                                                                  )
                                                             ((equal? type2 'Int) (let((t2 (update-env Expression1 'Int env)))
                                                                                    ;(extend-env Expression1 'Int env)
                                                                                    'Int
                                                                                    ;(cadr Expression1)
                                                                                    )
                                                                                  )
                                                             (else (let ((t1 (update-env Expression2 'Int env))
                                                                         (t2 (update-env Expression1 'Int env)))
                                                                     'Int))
                                                             )))
                                     (IfExpression (Token1 Token2 Expression1 Expression2 Expression3 Token3)
                                                   (let (
                                                         (t1 (eval-Expression Expression1 env))
                                                         (t2 (eval-Expression Expression2 env))
                                                         (t3 (eval-Expression Expression3 env)))
                                                       (if (and (equal? t1 'bool) (equal? t2 t3)) t3 (error "Type Error"))))
                                     (LetExpression (Token1 Token2 Token3 List Token4 Expression Token5)
                                                    (let* ((ids (get-ids List))
                                                           (exps (get-exps List))
                                                           (vals (map (lambda (Expression) (eval-Expression Expression env)) exps))
                                                           (new-env (extend-env-list ids vals env))
                                                           (new-normal-env (make-normal-env ids vals new-env)))
                                                      (eval-Expression Expression new-normal-env)))
                                     (Assignment (Token1 Token2 List Expression Token3)
                                                 (let ((id List)
                                                       (val (eval-Expression Expression env)))
                                                   (update-env id val env) ))
                                     (ProcedureExp (Token1 Token2 Token3 List Token4 Expression Token5)
                                                   (let* (
                                                         (new-env (extend-env-list List Expression env))
                                                         (new-normal-env (make-normal-env List Expression new-env))
                                                         )
                                                     (let((temp (eval-Expression Expression new-normal-env))
                                                          (vals (map (lambda (Exp) (eval-Expression Exp new-normal-env)) List)))
                                                     ;vals
                                                     ; temp
                                                     ;new-normal-env
                                                     (string->symbol (result vals (symbol->string temp)))
                                                     )))
                                     (Application (Token1 Expression List Token2)
                                                  (let* ((clos (deref-cell (eval-Expression Expression env)))
                                                         (ids (closure->formals clos))
                                                         (vals (map (lambda (Exp) (eval-Expression Exp env)) List))
                                                         (static-env (closure->env clos))
                                                         (new-env (extend-env-list ids vals static-env))
                                                         (body (closure->body clos))
                                                         (new-normal-env (make-normal-env ids body new-env)))
                                                    (eval-Expression body new-normal-env) ))
                                     (RecExpression (Token1 Token2 Token3 List Token4 Expression Token5)
                                                    (eval-Expression Expression (make-rec-env List env)))
                                     (Identifier (Token) (apply-env env Token))
                                     (else (error 'eval-Expression "Expression not found")))))
(define run
(lambda ()
	(record-case root
		(Goal (Expression Token)
		  (eval-Expression Expression (empty-env)))
		 (else (error 'run "Goal not found")))))
(run)
