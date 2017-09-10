#lang racket/base
(require
 "mk/mk.scm"
 rnrs/base-6
 rnrs/lists-6
 "chko.rkt"
 chk)

(define (takeo n args o)
  (conde
   [(== n 'lz)
    (== o '())]
   [(fresh (n^ B rest o^)
      (== n `(lsucc ,n^))
      (== args `(,B . ,rest))
      (== o `(,B . ,o^))
      (takeo n^ rest o^))]))

(define (dropo n args o)
  (conde
   [(== n 'lz)
    (== args o)]
   [(fresh (n^ B rest o^)
      (== n `(lsucc ,n^))
      (== args `(,B . ,rest))
      (dropo n^ rest o))]))

(chko
 #:out #:!c (q) '()
 (takeo 'lz '(1 2 3) q)

 #:out #:!c (q) '(1)
 (takeo '(lsucc lz) '(1 2 3) q)

 #:out #:!c (q) '(1 2)
 (takeo '(lsucc (lsucc lz)) '(1 2 3) q)

 #:out #:!c (q) '(1 2 3)
 (dropo 'lz '(1 2 3) q)

 #:out #:!c (q) '(2 3)
 (dropo '(lsucc lz) '(1 2 3) q))

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
             (evalo gamma^ ebody e^)))]))))

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


(define (inductiveo Delta A args p i D U)
  (let inductiveo ([A A]
                   [D D]
                   [args args]
                   [p p]
                   [i i])
    (conde
     [(fresh (T Gamma n)
             (== A D)
             (ind-entryo A Delta n T Gamma)
             (takeo n args p)
             (dropo n args i))]
     [(fresh (A^ B args^)
        (== `(,A^ ,B) A)
        (== `(,B . args^) args)
        (inductiveo A^ args D))])))

#;(define (inductive-decomposeo Delta A D p i U)
  (conde
   [()]))

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
        #;[(fresh (target motive methods A^ D C argsD motiveA i j Bs)
           (== `(elim ,target ,motive . ,methods) e)

           (applyo motive indices target A)

           (inductiveo Delta A^ args p i D `(Type ,j))
           (inductive-decomposeo Delta A^ D parameters indices `(Type ,j))

           (elimableo Delta motiveA parameters indices `(Type ,j) `(Type ,i))
           (branch-typeso Delta motive p i Bs)

           (typeo Gamma target gamma A^)
           (typeo Gamma motive gamma motiveA)
           )]))])))

(define (applyo f args t A)
  (== (list
       (for/fold ([f f])
                ([a args])
         `(,f ,a))
       t) A))

(define (branch-typeso Delta motive p i Bs)
  (conde
   [(== `())]))

;; Eliminate the type A, whoses parameters are p and indicies are i, from the universe U_f into the
;; universe U_t
(define (elimableo Delta A p i U_f U_t))

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
 #:subset #:n 8 #:!c (e) '(z (s z))
 (fresh (gamma)
        (typeo '((Nat . (0 (Type lz)
                           ((z . Nat)
                            (s . (Pi (x : Nat) Nat)))))) '()
                            e gamma 'Nat)))

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
