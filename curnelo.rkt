#lang racket/base
(require
 "mk/mk.scm"
 rnrs/base-6
 rnrs/lists-6
 "chko.rkt")



(define (varo e)
  (conde
   [(symbolo e)
    (=/= e 'elim)
    (=/= e 'Type)
    (=/= e 'closure)
    (=/= e 'lambda)
    (=/= e 'Pi)]))

(define deltao
  (lambda (x gamma term)
    (conde
     [(== '() gamma) (== x term)]
     [(fresh (y t gamma^)
        (== `((,y . ,t) . ,gamma^) gamma)
        (conde
         [(== x y) (== t term)]
         [(=/= x y) (deltao x gamma^ term)]))])))

(define ext-envo
  (lambda (gamma x e gamma^)
    (== `((,x . ,e) . ,gamma) gamma^)))

;; Meta-naturals; used for universe levels and parameters:
;; lz : Level
;; lsucc : Level -> Level
(define (levelo e)
  (conde
   [(== 'lz e)]
   [(fresh (e^)
      (== `(lsucc ,e^) e)
      (levelo e^))]))

(define (max-levelo i j k)
  (conde
   [(== 'lz i)
    (== j k)]
   [(== 'lz j)
    (== i k)]
   [(fresh (i^ j^ k^)
      (== i `(lsucc ,i^))
      (== j `(lsucc ,j^))
      (== k `(lsucc ,k^))
      (max-levelo i^ j^ k^))]))

(define Delta_Vec
  '((Vec . ((lsucc lz) (Pi (A : (Type lz))
                           (Pi (n : Nat)
                               (Type lz)))
                       ((nil . (Pi (A : (Type lz))
                                   ((Vec A) z)))
                        (cons . (Pi (A : (Type lz))
                                    (Pi (n : Nat)
                                        (Pi (a : A)
                                            (Pi (ls : ((Vec A) n))
                                                ((Vec A) (s n))))))))))
    (Nat . (lz (Type lz) ((z . Nat) (s . (Pi (x : Nat) Nat)))))))

(define evalo
  (lambda (Delta gamma e e^)
    (let evalo ([gamma gamma]
                [e e]
                [e^ e^])
      (conde
       [(fresh (i)
          (== `(Type ,i) e)
          (== `(Type ,i) e^))]
       [(varo e) (deltao e gamma e^)]
       [(fresh (A A^ B B^ gamma^ x)
          (== `(Pi (,x : ,A) ,B) e)
          (ext-envo gamma x x gamma^)
          (== `(Pi (,x : ,A^) ,B^) e^)
          (evalo gamma A A^)
          (evalo gamma^ B B^))]
       [(fresh (x A ebody ebody^)
          (== `(lambda (,x : ,A) ,ebody) e)
          (== `(closure ,gamma (,x : ,A) ,ebody^) e^)
          (evalo gamma ebody ebody^))]
       [(fresh (e1 e2 e2^ x A ebody env)
          (== `(,e1 ,e2) e)
          (evalo gamma e1
                 `(closure ,env (,x : ,A) ,ebody))
          (evalo gamma e2 e2^)
          (fresh (gamma^)
            (ext-envo gamma
                      x
                      e2^
                      gamma^)
            (evalo gamma^ ebody e^)))]
       [(fresh (target^ c args D n A Gamma)
          (== `(elim ,target ,motive . ,branches) e)
          (evalo gamma target target^)
          (applyo c args target^)
          (ind-entryo D Delta n A Gamma)
          (mapcaro Gamma Constrs)
          (list-refo i Constrs c)
          (list-refo i branches b_i)
          (assoco c Gamma c_type)
          (recursive-positionso D c_type c rps)
          (make-recursiono args rps recursive)
          (appendo args recursive bargs)
          (applyo b_i bargs branch)
          (evalo gamma branch e^))]))))

(chko
 #:out #:!c (q) '(Type lz)
 (evalo '() '() '((lambda (x : (Type (lsucc lz))) x) (Type lz)) q)

 #:out #:!c (q) 'x
 (evalo '() '() 'x q)

 #:out #:!c (q) '(closure () (x : (Type lz)) x)
 (evalo '() '()
        '((lambda (f : (Pi (x : (Type lz)) (Type lz))) f)
          (lambda (x : (Type lz)) x))
        q)

 #:= #:n 5 #:!c (q)
 '(x
   ((lambda (_.0 : _.1) x) (Type _.2))
   ((lambda (_.0 : _.1) _.0) x)
   ((lambda (_.0 : _.1) x) _.2)
   ((lambda (_.0 : _.1) x) (lambda (_.2 : _.3) (Type _.4))))
 (evalo '() '() q 'x)

 #:= #:n 5 #:!c (q)
 '((Type _.0)
   _.0
   (Pi (_.0 : (Type _.1)) (Type _.2))
   (Pi (_.0 : _.1) (Type _.2))
   (Pi (_.0 : (Type _.1)) _.0))
 (evalo '() '() q q))

;; Delta := . | Ind(Var : n A Gamma)
;; ((Var . (n A Gamma)) . Delta)
(define (ind-lookupo x Delta A)
  (conde
   [(fresh (y n Gamma Delta^)
      (== `((,y . (,n ,A ,Gamma)) . ,Delta^) Delta)
      (== x y))]
   [(fresh (y n Gamma Delta^ A^)
      (== `((,y . (,n ,A^ ,Gamma)) . ,Delta^) Delta)
      (=/= x y)
      (lookupo x Gamma A))]
   [(fresh (y n Gamma Delta^ A^)
      (== `((,y . (,n ,A^ ,Gamma)) . ,Delta^) Delta)
      (=/= x y)
      (ind-lookupo x Delta^ A))]))

(define (ind-entryo x Delta n A Gamma)
  (conde
   [(fresh (Delta^)
      (== `((,x . (,n ,A ,Gamma)) . ,Delta^) Delta))]
   [(fresh (n^ A^ Gamma^ Delta^ y)
      (=/= x y)
      (== `((,y . (,n^ ,A^ ,Gamma^)) . ,Delta^) Delta)
      (ind-entryo x Delta^ n A Gamma))]))

(chko
#:out #:n 1 #:!c (n T Gamma) '((lsucc lz) (Pi (A : (Type lz))
                                               (Pi (n : Nat)
                                                   (Type lz)))
                                           ((nil . (Pi (A : (Type lz))
                                                       ((Vec A) z)))
                                            (cons . (Pi (A : (Type lz))
                                                        (Pi (n : Nat)
                                                            (Pi (a : A)
                                                                (Pi (ls : ((Vec A) n))
                                                                    ((Vec A) (s n)))))))))
 (ind-entryo 'Vec Delta_Vec n T Gamma)

 #:out #:n 1 #:!c (n T Gamma) '(lz (Type lz) ((z . Nat) (s . (Pi (x : Nat) Nat))))
 (ind-entryo 'Nat Delta_Vec n T Gamma))

(define (telescope-resulto T U)
  (conde
   [(fresh (x A B)
      (== T `(Pi (,x : ,A) ,B))
      (telescope-resulto B U))]
   [(fresh (i)
      (== T `(Type ,i))
      (== U T))]))

(chko
 #:out #:n 2 #:!c (U) '(Type lz)
 (telescope-resulto '(Pi (x : Nat) (Type lz)) U)

 #:out #:n 2 #:!c (U) '(Type lz)
 (telescope-resulto '(Type lz) U)

 #:out #:n 2 #:!c (U) '(Type lz)
 (telescope-resulto '(Pi (y : Nat) (Pi (x : Nat) (Type lz))) U))

(define (inductiveo Delta T D p i)
  (fresh (args)
    (let inductiveo ([T T]
                     [args^ args])
      (conde
       [(fresh (Gamma n A)
          (== args^ '())
          (== T D)
          (ind-entryo D Delta n A Gamma)
          ;; TODO: Write a splito relation.
          (dropo n args p) ; opposite of intuition since we built the list backwards
          (takeo n args i))]
       [(fresh (T^ B args^^)
          ;; TODO This is way too clever
          (== `(,T^ ,B) T)
          (== `(,B . ,args^^) args^)
          (inductiveo T^ args^^))]))))
(chko
 #:out #:n 2 #:!c (p i) '(() ())
 (inductiveo '((Nat . (lz (Type lz) ((z . Nat) (s . (Pi (x : Nat) Nat))))))
             'Nat 'Nat p i)

 #:out #:n 2 #:!c (p i D) '(() () Nat)
 (inductiveo '((Nat . (lz (Type lz) ((z . Nat) (s . (Pi (x : Nat) Nat))))))
             'Nat D p i)

 #:out #:n 2 #:!c (p i) '((Nat) (z))
 (inductiveo Delta_Vec '((Vec Nat) z) 'Vec p i)

 #:out #:n 2 #:!c (p i D) '((Nat) (z) Vec)
 (inductiveo Delta_Vec '((Vec Nat) z) D p i))

(define (recursive-positionso D type c rps)
  (let loop ([type type] [rps rps])))

;; Well-formed inductive declarations stub:
;; TODO: Strict positivity
;; TODO: well-typed types
(define (wf Delta)
  (== Delta Delta))

(define typeo
  (lambda (Delta Gamma e gamma A)
    (conde
     [(wf Delta)
      (let typeo ([Gamma Gamma]
                  [e e]
                  [gamma gamma]
                  [A A])
        (conde
         [(fresh (i)
            (== `(Type ,i) e) ;; T-Type
            (levelo i)
            (== `(Type (lsucc ,i)) A))]
         [(varo e) ;; T-Var
          (lookupo e Gamma A)]
         [(varo e) ;; T-Constr/Ind
          (ind-lookupo e Delta A)]
         [(fresh (x A^ B Gamma^ gamma^ i) ;; T-Pi-Prop
            (== `(Pi (,x : ,A^) ,B) e)
            (ext-envo Gamma x A^ Gamma^)
            (ext-envo gamma x x gamma^)
            (== A `(Type lz))
            (typeo Gamma A^ gamma `(Type ,i))
            (typeo Gamma^ B gamma^ `(Type lz)))]
         [(fresh (x A^ B Gamma^ gamma^ i j k) ;; T-Pi-Type
            (== `(Pi (,x : ,A^) ,B) e)
            (ext-envo Gamma x A^ Gamma^)
            (ext-envo gamma x x gamma^)
            (== A `(Type ,k))
            (max-levelo i j k)
            (typeo Gamma A^ gamma `(Type ,i))
            (typeo Gamma^ B gamma^ `(Type ,j)))]
         [(fresh (x A^ body B Gamma^ gamma^ i) ;; T-Lam
            (== `(lambda (,x : ,A^) ,body) e)
            (== `(Pi (,x : ,A^) ,B) A)
            (ext-envo Gamma x A^ Gamma^)
            (ext-envo gamma x x gamma^)
            (typeo Gamma A^ gamma `(Type ,i))
            (typeo Gamma^ body gamma^ B))]
         [(fresh (e1 e2 A^ B gamma^^ gamma^ x) ;; T-App
            ;; I suspect this could use more constraints to allow typeo to return different subgammas
            ;; from type-checko, but I'll sort that out later.
            ;; Unification might just do the right thing
            (== `(,e1 ,e2) e)
            (ext-envo gamma^ x e2 gamma)
            (type-checko Delta Gamma e2 gamma^ A^)
            (typeo Gamma e1 gamma^ `(Pi (,x : ,A^) ,B))
            (== A B))]
         [(fresh (target motive methods A^ D D_p C argsD motiveA i j Bs parameters indices tmp gamma^
                         A_p motiveA^)
              (== `(elim ,target ,motive . ,methods) e)

              (applyo motive indices tmp)
              (== `(,tmp ,target) A)

              (inductiveo Delta A^ D parameters indices)

              (applyo D parameters D_p)
              (typeo Gamma D_p gamma^ A_p)
              (motive-typeo A_p D_p motiveA^)

              #;(branch-typeso Delta Gamma motive p i Bs)

              (typeo Gamma target gamma A^)
              (type-checko Delta Gamma motive gamma^ motiveA^)
              )]))])))

;; f (e ...) -> (f e ...)
;; but curried
(define (applyo rator rands app)
  (let loop ([rator rator] [rands rands])
    (conde
     [(== '() rands)
      (== rator app)]
     [(fresh (rand rator^ rands^)
        (== `(,rand . ,rands^) rands)
        (== `(,rator ,rand) rator^)
        (loop rator^ rands^))])))

(define (branch-typeso Delta motive p i Bs)
  (conde
   [(== `())]))

(define (instantiateo Pi args gamma A)
  (let loop ([Pi Pi]
             [args args]
             [gamma^ '()])
    (conde
     [(fresh (x A^ B e args^)
        (== `(Pi (,x : ,A^) ,B) Pi)
        (== `(,e . ,args^) args)
        (loop B args^ `((,x . ,e) . ,gamma^)))]
     [(fresh ()
        (== '() args)
        (== gamma gamma^)
        (== Pi A))])))

(chko
 #:out #:n 1 #:!c (gamma A) '(((x . Nat)) (Type 1))
 (instantiateo '(Pi (x : (Type 1)) (Type 1)) '(Nat) gamma A)

 #:out #:n 1 #:!c (gamma A) '(((x . Nat)) (Pi (a : x) x))
 (instantiateo '(Pi (x : (Type 1)) (Pi (a : x) x)) '(Nat) gamma A))

;; Given the type AD of the inductive type, the parameters p and the indicies i, what is the expected
;; type of the motive B?
;; Remember that due to dependency, B will be in under the substitution gamma.
;;
;; D p ... : Π (xⱼ : Aⱼ ...). Type = A
;; motive : Π (xⱼ : Aⱼ ... _ : (D pᵢ ... xⱼ ...)). Type
(define (motive-typeo A D_p B)
  (let loop ([A A] [D D_p] [B B])
    (conde
     [(fresh (x A^ A_i B^)
        (== A `(Pi (,x : ,A_i) ,A^))
        (== B `(Pi (,x : ,A_i) ,B^))
        (loop A^ `(,D_p ,x) B^))]
     [(fresh (x j i)
        (== A `(Type ,i))
        (== B `(Pi (,x : ,D) (Type ,j))))])))

(chko
 #:out #:n 1 #:!c (B) '(Pi (_.0 : Nat) (Type _.1))
 (motive-typeo '(Type 0) 'Nat B)
 #:out #:n 1 #:!c (B) '(Pi (n : Nat) (Pi (_.0 : ((Vec Nat) n)) (Type _.1)))
 (motive-typeo '(Pi (n : Nat) (Type 0)) '(Vec Nat) B))

;; Need infer/check distinction for algorithmic interpretation.
(define (type-checko Delta Gamma e gamma A)
  (fresh (B) ;; T-Conv
    (typeo Delta Gamma e gamma B)
    (evalo Delta gamma B A)))

(define lookupo
  (lambda (x gamma term)
    (fresh (y t gamma^)
      (== `((,y . ,t) . ,gamma^) gamma)
      (conde
       [(== x y) (== t term)]
       [(=/= x y) (lookupo x gamma^ term)]))))

(require racket/function)
(chko
 #:out #:!c (q) '(Type (lsucc lz))
 (typeo '() '() '(Type lz) '() q)

 #:= (q) '()
 (typeo '() '() 'z '() q)

 #:out #:!c (q) '(Type lz)
 (typeo '() '((z . (Type lz))) 'z '() q)

 #:out #:!c (q) '(Pi (x : (Type lz)) (Type lz))
 (typeo '() '() '(lambda (x : (Type lz)) x) '() q)

 #:= (q gamma) '()
 (typeo '() '() '((lambda (x : (Type lz)) (Type lz)) (Type lz)) gamma q)

 #:out #:!c (q gamma) '((Type (lsucc lz)) ((x . (Type lz)) . _.0))
 (typeo '() '() '((lambda (x : (Type (lsucc lz))) (Type lz)) (Type lz)) gamma q)

 #:out #:!c (q gamma) '((Type (lsucc lz)) ((x . (Type lz)) . _.0))
 (typeo '() '() '((lambda (x : (Type (lsucc lz))) x) (Type lz)) gamma q)

 #:out #:!c (q) '(Pi (A : (Type lz)) (Pi (a : A) A))
 (typeo '() '() '(lambda (A : (Type lz))
                   (lambda (a : A)
                     a)) '() q)

 ;; Try inferring some types
 #:in #:n 5 #:!c (q ?1 ?2) '((Pi (A : (Type lz)) (Pi (a : A) A)) (Type lz) A)
 (typeo '() '() `(lambda (A : ,?1)
                   (lambda (a : ,?2)
                     a)) '() q)

 ;; Try inferring some terms
 #:in #:n 2 #:!c (e) '(lambda (A : (Type lz))
                        (lambda (a : A)
                          a))
 (typeo '() '() e '() `(Pi (A : (Type lz)) (Pi (a : A) A)))

 ;; Check dependent application
 #:in #:n 1 #:!c (q) '(Pi (a : (Type lz)) (Type lz))
 (fresh (gamma ?1 q1)
   (typeo '() '() `((lambda (A : ,?1)
                      (lambda (a : A)
                        a))
                    (Type lz)) gamma q1)
   (evalo '() gamma q1 q))

 ;; Check conversion
 #:in #:n 1 #:!c (q) '(Pi (a : (Type lz)) (Type lz))
 (fresh (gamma ?1)
   (type-checko '() '() `((lambda (A : ,?1)
                            (lambda (a : A)
                              a))
                          (Type lz)) gamma q))

 ;; Check False as a concept
 #:out #:n 1 #:!c (q) '(Type lz)
 (type-checko '() '() `(Pi (α : (Type lz)) α) '() q)

 ;; Prove me some Nats
 #:subset #:n 5 #:!c (e) '(z (s z))
 (fresh (gamma)
   (typeo '() '((z . Nat) (s . (Pi (x : Nat) Nat)) (Nat . (Type lz)))
          e gamma 'Nat))

 ;; Inductive tests
 #:subset #:n 8 #:!c #:t 10 (e) '(z (s z))
 (fresh (gamma)
   (typeo '((Nat . (0 (Type lz)
                      ((z . Nat)
                       (s . (Pi (x : Nat) Nat)))))) '()
          e gamma 'Nat))

 ; linear time implementation of zero.
 #:out #:n 1 #:!c (gamma A) '(_.0 ((lambda (x : Nat) Nat) z))
 (typeo Delta_Vec '() '(elim z (lambda (x : Nat) Nat) z (lambda (x : Nat) (lambda (ih : Nat) ih)))
        gamma A)

 #:out #:n 1 #:!c (gamma) '()
 (type-checko Delta_Vec '() '(elim z (lambda (x : Nat) Nat) z (lambda (x : Nat) (lambda (ih : Nat) ih)))
        gamma 'Nat))

;; Prove False

;; Have been run for 60 seconds
#;(chko
   #:= #:t 60 (e) '((()))
   (typeo '() '() e '() '(Pi (α : (Type lz)) α))

   ;; Prove False under some assumptions
   #:= #:t 60 (e) '((()))
   (typeo '((f . (Pi (A : (Type lz))
                     (Pi (B : (Type lz))
                         (Pi (_ : A) B))))
            (z . Nat)
            (s . (Pi (n : Nat) Nat))
            (Nat . (Type lz))) e '() '(Pi (α : (Type lz)) α)))

;; Local Variables:
;; eval: (put 'fresh 'racket-indent-function 'defun)
;; End:
