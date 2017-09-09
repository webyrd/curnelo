#lang racket/base
(require
 "mk/mk.scm"
 rnrs/base-6
 rnrs/lists-6
 chk)

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

(define evalo
  (lambda (gamma e e^)
    (conde
      [(== '(Type) e) (== '(Type) e^)]
      [(symbolo e) (deltao e gamma e^)]
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
           (evalo gamma^ ebody e^)))])))

(chk
 (run* (q)
       (evalo '() '((lambda (x : (Type)) x) (Type)) q))
 '(((Type)))

 (run* (q)
       (evalo '() 'x q))
 '((x))

 (run* (q)
       (evalo '()
              '((lambda (f : (Pi (x : (Type)) (Type))) f)
                (lambda (x : (Type)) x))
              q))
 '(((closure () (x : (Type)) x)))

 (run 5 (q)
      (evalo '() q 'x))
 '((x)
   (((lambda (_.0 : _.1) x) (Type))
    (=/= ((_.0 x))))
   (((lambda (_.0 : _.1) _.0) x)
    (sym _.0))
   (((lambda (_.0 : _.1) x) _.2)
    (=/= ((_.0 x))) (sym _.2))
   (((lambda (_.0 : _.1) x) (Pi (_.2 : (Type)) (Type)))
    (=/= ((_.0 x)))))

 (run 5 (q)
      (evalo '() q q))
 '(((Type))
   (_.0 (sym _.0))
   ((Pi (_.0 : (Type)) (Type)))
   ((Pi (_.0 : _.1) (Type)) (sym _.1))
   ((Pi (_.0 : (Type)) _.0) (sym _.0))))

(define typeo
  (lambda (Gamma e gamma A)
    (conde
      [(== '(Type) e) ;; T-Type
       (== '(Type) A)]
      [(symbolo e) ;; T-Var
       (lookupo e Gamma A)]
      [(fresh (x A^ B Gamma^ gamma^) ;; T-Pi
         (== `(Pi (,x : ,A^) ,B) e)
         (ext-envo Gamma x A^ Gamma^)
         (ext-envo gamma x x gamma^)
         (== A '(Type))
         (typeo Gamma A^ gamma '(Type))
         (typeo Gamma^ B gamma^ '(Type)))]
      [(fresh (x A^ body B Gamma^ gamma^)
         (== `(lambda (,x : ,A^) ,body) e)
         (== `(Pi (,x : ,A^) ,B) A)
         (ext-envo Gamma x A^ Gamma^)
         (ext-envo gamma x x gamma^)
         (typeo Gamma A^ gamma '(Type))
         (typeo Gamma^ body gamma^ B))]
      [(fresh (e1 e2 A^ B gamma^^ gamma^ x)
         ;;; TODO FIXME!
         (== `(,e1 ,e2) e)
         (ext-envo gamma^^ x e2 gamma)
         (typeo Gamma e1 gamma^^ `(Pi (,x : ,A^) ,B))
         (typeo Gamma e2 gamma^ A^)
         (== A B))]
      )))

(define lookupo
  (lambda (x gamma term)
    (fresh (y t gamma^)
      (== `((,y . ,t) . ,gamma^) gamma)
      (conde
        [(== x y) (== t term)]
        [(=/= x y) (lookupo x gamma^ term)]))))


(chk
 (run* (q)
       (typeo '() '(Type) '() q))
 '(((Type)))

 (run* (q)
       (typeo '() 'z '() q))
 '()

 (run* (q)
       (typeo '((z . (Type))) 'z '() q))
 '(((Type)))

 (run* (q) (typeo '() '(lambda (x : (Type)) x) '() q))
 '(((Pi (x : (Type)) (Type))))

 (run* (q)
       (typeo '() '((lambda (x : (Type)) (Type)) (Type)) '() q))
 '(((Type)))

 (run* (q)
       (typeo '() '((lambda (x : (Type)) x) (Type)) '() q))
 '(((Type))))
