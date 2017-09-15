#lang racket/base
(require
 "mk/mk.scm"
 rnrs/base-6
 rnrs/lists-6
 "chko.rkt")

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

(define (list-refo n ls o)
  (let loop ([n n] [ls ls])
    (conde
     [(fresh (args)
        (== n 'lz)
        (== `(,o . ,args) ls))]
     [(fresh (ln args e)
        (== n `(lsucc ,ln))
        (== `(,e . ,args) ls)
        (loop ln args))])))

(chko
 #:out #:!c (q) 1
 (list-refo 'lz '(1 2 3) q)

 #:out #:!c (q) 2
 (list-refo '(lsucc lz) '(1 2 3) q)

 #:out #:!c (q) 3
 (list-refo '(lsucc (lsucc lz)) '(1 2 3) q))

(define (mapcaro ls o)
  (let loop ([ls ls] [o^ o])
    (conde
     [(== ls '())
      (== o^ '())]
     [(fresh (ls^ rest o^^ y)
        (== `((,y . ,rest) . ,ls^) ls)
        (== `(,y . ,o^^) o^)
        (loop ls^ o^^))])))

(chko
 #:out #:!c (q) '(1 2 4)
 (mapcaro '((1) (2 3) (4 . (5))) q))

(define (assoco v ls o)
  (let loop ([ls ls])
    (conde
     [(fresh (ls^)
        (== `((,v . ,o) . ,ls^) ls))]
     [(fresh (ls^ car)
        (== `(,car . ,ls^) ls)
        (loop ls^))])))

(chko
 #:out #:!c (q) 'Nat
 (assoco 'z '((z . Nat)
              (s . (Pi (x : Nat) Nat))) q)

 #:out #:!c (q) '(Pi (x : Nat) Nat)
 (assoco 's '((z . Nat)
              (s . (Pi (x : Nat) Nat))) q))

(define (appendo ls1 ls2 o)
  (let loop ([ls1 ls1] [ls2 ls2])
    (conde
     [(== ls2 '())
      (== ls1 o)]
     [(fresh (ls1^ ls2^ x)
        (== `(,x . ,ls2^) ls2)
        (snoco ls1^ x ls1)
        (loop ls1^ ls2^))])))

(define (reverseo ls o)
  (conde
   [(== ls '())
    (== o ls)]
   [(fresh ()
      (== `(,x . ,ls^) ls)
      (loop ls^ o^))]))
(define (snoco ls x o)
  (reverseo ls o^)
  (== o^^ `(,x . ,ls))
  (reverseo o^^ o))

(chko
 #:out #:!c (q) '(1 2 3 4 5 6)
 (appendo '(1 2 3) '(4 5 6) q))

