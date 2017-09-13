#lang racket

(require
 "mk/mk.scm"
 chk
 compatibility/mlist
 (for-syntax racket/base syntax/parse))

(provide chko)

#|
(chko
   each kind of test can take any of the following optional modifiers:
     #:n n:nat -- Run the query until n results are produced. Default to *
     #:t n:nat -- Run the query until t seconds have passed, or until completion. Default to
 infinite.
     #:!c      -- Filter the constraint set out before checking that the expected matches the actual.

  An #:= test checks that the (one) expected value is equal? to the output of the result of running,
 via run, the actual expression.
    #:= #:n 1 (q) '(((Type lz)))
    (evalo '() q '() q))

  An #:out test checks that each expected value is equal? to the output of the corresponding query
variable.
    #:out #:n 1 (q gamma) '((Type lz)) '()
    (evalo '() q gamma q))

  An #:in test checks that the expected value is a member of the set of outputs produced by the
corresponding query.
    #:in #:n 5 (q) '((Type lz))
    (evalo '() q q))

  #:in #:n 5 #:!c (q) '(Type lz)
  (evalo '() q q))

  #:= #:t 30 (e) '()
  (typeo '() e '() '(Pi (α : (Type lz)) α))
 |#

(define (mdrop-right mlist pos)
  (mreverse (mcdr (mreverse mlist))))

(define (filter-constraints res-set)
  (mmap (lambda (x) (mcar x)) res-set))

(define (timeout n default th)
  (define ch (make-channel))
  (define t (thread (lambda () (channel-put ch (th)))))
  (if (sync/timeout n ch)
      (channel-get ch)
      (begin
        (kill-thread t)
        default)))

(define ((check-mmember expected) ls)
  (and (mmember expected ls) #t))

(define ((check-msublist expected) ls)
  (for/fold ([r #t])
            ([y expected])
    (and (mmember y ls) r)))

(begin-for-syntax
  (define (make-run vars n test timeout expect filter-constraints?)
    (define run
      (quasisyntax/loc test
        (#,@(if n (quasisyntax/loc n (run #,n)) (quasisyntax/loc test (run*)))
         #,vars
         #,test)))
    (define filtered-run
      (if filter-constraints?
          (quasisyntax/loc test
            (filter-constraints #,run))
          run))
    (if timeout
        (quasisyntax/loc timeout
          (timeout #,timeout #,expect (lambda () #,filtered-run)))
        filtered-run))

  (define (make-chk-test flag actual expected)
    (syntax-parse flag
      [#:subset
       (quasisyntax/loc flag
         (#:? (check-msublist #,expected) #,actual))]
      [#:=
       (quasisyntax/loc flag
         (#,actual #,expected))]
      [#:out
       (quasisyntax/loc flag
         (#,actual #,(quasisyntax/loc expected
                       (mlist #,expected))))]
      [#:in
       (quasisyntax/loc flag
         (#:? (check-mmember #,expected) #,actual))]))

  (define-syntax-class test-flag
    (pattern (~or #:= #:out #:in #:subset)))

  (define-splicing-syntax-class testo
    (pattern
     (~seq flag:test-flag
           (~optional (~seq #:n n:nat))
           (~optional (~and #:!c (~bind (filter-constraints? #t))))
           (~optional (~seq #:t t:nat))
           (query-variable:id ...) expected-value
           test:expr)
;     #:fail-when (and (memq (syntax-e #'flag) '(#:in #:out))
;                      (= (length (attribute query-variable))
;                         (length (attribute expected-value))))
;     (raise-syntax-error 'chko
;                         (format
;                          "For ~a tests, there must be the same number of query variables as expected values."
;                          (syntax-e #'flag))
;                         this-syntax
;                         (quasisyntax/loc this-syntax
;                           (query-variable ...))
;                         (list (attribute expected-value)))
;
;     ;; TODO: Support testing each query variable against a subset
;     #:fail-when (and (memq (syntax-e #'flag) '(#:= #:subset))
;                      (not (= (length (attribute expected-value)) 1)))
;     (raise-syntax-error 'chko
;                         (format "For ~a tests, there must be exactly 1 expected value."
;                                 (syntax-e #'flag))
;                         this-syntax
;                         (attribute expected-value))

     #:attr expected (attribute expected-value)
     #:attr actual (make-run (attribute query-variable)
                             (attribute n)
                             (attribute test)
                             (attribute t)
                             (attribute expected)
                             (attribute filter-constraints?))
     #:attr chk-test (make-chk-test (attribute flag) (attribute actual) (attribute expected)))))

(define-syntax (chko syn)
  (syntax-parse syn
    [(_ t:testo)
     (quasisyntax/loc syn (chk #,@(quasisyntax/loc t t.chk-test)))]
    [(_ r ... t:testo)
     (quasisyntax/loc syn
       (chk*
        #,(quasisyntax/loc syn
            (chko r ...))
        (chk #,@(quasisyntax/loc t t.chk-test))))]))
