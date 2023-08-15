(define-record Goal (Expression Token))
(define-record IntegerLiteral (Token))
(define-record TrueLiteral (Token))
(define-record FalseLiteral (Token))
(define-record PlusExpression (Token1 Token2 Expression1
   Expression2 Token3))
(define-record IfExpression (Token1 Token2 Expression1
   Expression2 Expression3 Token3))
(define-record LetExpression (Token1 Token2 Token3
   List Token4 Expression Token5))
(define-record Identifier (Token))
(define-record Assignment (Token1 Token2 Identifier
   Expression Token3))
(define-record closure (formals body env))
(define-record ProcedureExp (Token1 Token2 Token3
   List Token4 Expression Token5))
(define-record Application (Token1 Expression List
   Token2))
(define-record RecExpression (Token1 Token2 Token3
   List Token4 Expression Token5))
(define-record Declaration (Token1 Identifier Expression
   Token2))
(define-record RecDeclaration (Token1 Identifier ProcedureExp
   Token2))
(define-record rec-env (recdecl-list env))
(define-record normal-env (ids vals env))
(define-record App (exps env))
