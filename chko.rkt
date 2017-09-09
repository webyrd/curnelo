#lang racket

(require
 "mk/mk.scm"
 chk
 compatibility/mlist
 (for-syntax racket/base syntax/parse))

(provide chko)

#|
(chko
  #:= (q) '(((Type lz))) ; an #:= test just tests for equality
  #:n 1                  ; all tests take an optional number of test, which defauts to *
  (evalo '() q '() q))

  #:out (q gamma) '((Type lz)) '() ; an #:out test checks equality against the variable(s)
  #:n 1
  (evalo '() q gamma q))

  #:in (q) '((Type lz)) ; an #:in tests that the given values are members of the output variable
  #:n 5
  (evalo '() q q))

  #:in (q) '(Type lz)
  #:n 5 #:!c              ; the optional #:!c flag ignores the constraint list when checking
  (evalo '() q q))

  #:= (e) '()
  #:t 30                 ; the optional #:t flag ignores the specifies a timeout after which the test
is assumed to pass
  (typeo '() e '() '(Pi (α : (Type lz)) α))
 |#

(define (mdrop-right mlist pos)
  (mreverse (mcdr (mreverse mlist))))

(require racket/trace)
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

(begin-for-syntax
  (define (make-run vars n test timeout expect filter-constraints?)
    (define run
      #`(#,@(if n #`(run #,n) #'(run*))
         #,vars
         #,test))
    (define filtered-run
      (if filter-constraints?
          #`(filter-constraints #,run)
          run))
    (if timeout
        #`(timeout #,timeout #,expect (lambda () #,filtered-run))
        filtered-run))

  (define (make-chk-test flag actual expected)
    (syntax-parse flag
      [#:=
       #`(#,actual #,expected)]
      [#:out
       #`(#,actual (mlist #,expected))]
      [#:in
       #`(#:? (lambda (x)
            (for/fold ([r #t])
                      ([y #,expected])
              (and (mmember y x) r)))
          #,actual)]))

  (define-syntax-class test-flag
    (pattern (~or #:= #:out #:in)))

  (define (out-test? flag)
    (syntax-parse flag [#:out #t] [else #f]))

  (define (=-test? flag)
    (syntax-parse flag [#:= #t] [else #f]))

  (define-splicing-syntax-class testo
    (pattern
     (~seq flag:test-flag (query-variable:id ...) expected-value
           (~optional (~seq #:n n:nat))
           (~optional (~and #:!c (~bind (filter-constraints? #t))))
           (~optional (~seq #:t t:nat))
           test:expr)
;     #:fail-when (and (=-test? (attribute flag))
;                        (not (= (length (attribute expected-value)) 1)))
;     (raise-syntax-error 'chko
;                         "For #:= tests, there must be exactly 1 expected value"
;                         this-syntax
;                         #'expected-value)
;     #:fail-when (and (out-test? (attribute flag))
;                        (= (length (attribute query-variable)) (length (attribute expected-value))))
;     (raise-syntax-error 'chko
;                         "For #:out tests, there must be the same number of query variables as expected values"
;                         this-syntax
;                         #'(query-variable ...)
;                         (list #'(expected-value ...)))
     #:attr expected (attribute expected-value)
     #:attr actual (make-run (attribute query-variable)
                             (attribute n)
                             (attribute test)
                             (attribute t)
                             (attribute expected)
                             (attribute filter-constraints?))
     #:attr chk-test (make-chk-test (attribute flag) (attribute actual) (attribute expected)))))

(begin-for-syntax
  (require racket/trace (for-template racket/trace))
  (define (maybe-syntax->datum x)
    (if (syntax? x)
        (syntax->datum x)
        x))
  (current-trace-print-args
   (let ([ctpa (current-trace-print-args)])
     (lambda (s l kw l2 n)
       (ctpa s (map maybe-syntax->datum l) kw l2 n))))
  (current-trace-print-results
   (let ([ctpr (current-trace-print-results)])
     (lambda (s l n)
       (ctpr s (map maybe-syntax->datum l) n)))))
(define-syntax (chko syn)
  (syntax-parse syn
    [(_ t:testo)
     #`(chk #,@(attribute t.chk-test))]
    [(_ r ... t:testo)
     #`(chk*
        (chko r ...)
        (chk #,@(attribute t.chk-test)))]))

