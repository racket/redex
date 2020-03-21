(#rx"define-language:.*expression context"
 ([illegal-def (define-language L)])
 (values illegal-def))

(#rx"define-language:.*unquote disallowed"
 ([illegal-unquote ,3])
 (let ()
   (define-language L
     (n illegal-unquote))
   (void)))

; error message shows correct form name
(#rx"define-extended-language:.*underscore"
 ([bad-underscore y_1])
 (let ()
   (define-language L)
   (define-extended-language M L
     (z () (1 bad-underscore)))
   (void)))

(#rx"expected an identifier" ([not-id (L)]) (define-language not-id))
(#rx"expected at least one production" ([separator ::=]) (define-language L (x separator)))
(#rx"expected at least one production" ([nt x]) (define-language L (nt)))
(#rx"expected at least one production" ([nt-pos (x)]) (define-language L (nt-pos)))
(#rx"expected preceding non-terminal names" ([separator ::=]) (define-language L (separator a b)))
(#rx"expected non-terminal name" ([not-nt (y)]) (define-language L (x not-nt ::= z)))
(#rx"expected production" ([not-prod ::=]) (define-language L (x ::= y not-prod z)))
(#rx"expected non-terminal definition" ([not-def q]) (define-language L not-def))
(#rx"expected non-terminal definition" ([not-def ()]) (define-language L not-def))

(#rx"the non-terminal e is defined in terms of itself\n[^\n]*at: e\n"
 ([e1 e]) (define-language L (e1 ::= e)))
(#rx"the non-terminal e is defined in terms of itself\n[^\n]*at: e\n"
 ([e1 e]) (define-language L (e1 e)))
(#rx"found a cycle of non-terminals that doesn't consume input"
 ([a1 a] [b1 b]) (define-language L (a1 ::= b) (b1 ::= a)))

(#rx"unknown name imported or exported: y"
 ([bf (λ (x) e #:refers-to y)])
 (define-language l
   #:binding-forms
   bf))

(#rx"define-extended-language: cannot extend the `B` non-terminal because the language L does not define it"
 ([dots ....])
 (let ()
   (define-language L
     (A ::= a b c d))
   (define-extended-language L2 L
     (B ::= dots x y z w))
   (void)))


(#rx"the non-terminal B is defined in terms of itself"
 ([B1 B])
 (define-language test
   (B1 ::= (in-hole A B))
   (A ::= hole)))
(#rx"found a cycle of non-terminals that doesn't consume input: A B C D"
 ([A1 A][B1 B][C1 C][D1 D])
 (define-language test
   (A1 ::= B)
   (B1 ::= C)
   (C1 ::= D)
   (D1 ::= A)))
(#rx"the non-terminal B is defined in terms of itself"
 ([B1 B])
 (let ()
   (define-language test)
   (define-extended-language test2 test
     (B1 ::= (in-hole A B))
     (A ::= hole))
   (void)))
(#rx"the non-terminal B is defined in terms of itself"
 ([B1 B])
 (let ()
   (define-language test
     (A ::= hole))
   (define-extended-language test2 test
     (B1 ::= (in-hole A B)))
   (void)))
(#rx"the non-terminal B is defined in terms of itself"
 ([B1 B])
 (let ()
   (define-language test
     (A ::= hole))
   (define-extended-language test2 test
     (B1 ::= (in-hole A B))
     (A ::= .... (hole 2)))
   (void)))
(#rx"found a cycle of non-terminals that doesn't consume input"
 ([DL (define-union-language test3
        test1
        test2)])
 (let ()
   (define-language test1
     (A ::= B)
     (B ::= b))
   (define-language test2
     (A ::= a)
     (B ::= A))
   DL
   (void)))
(#rx"found a cycle of non-terminals that doesn't consume input"
 ([P1 p][E1 e])
 (let ()
   (define-language L1
     [P1 ::= e]
     [e ::= 1])
   (define-extended-language L2 L1
     [E1 ::= .... p])
   (void)))
