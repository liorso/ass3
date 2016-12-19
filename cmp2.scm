;;; qq.scm
;;; A naive, one-level quasiquote implementation + optimizations
;;;
;;; Programmer: Mayer Goldberg, 2016
(load "compiler1.scm")
(load "pattern-matcher.scm")

;;;

(define ^quote?
  (lambda (tag)
    (lambda (e)
      (and (pair? e)
           (eq? (car e) tag)
           (pair? (cdr e))
           (null? (cddr e))))))

(define quote? (^quote? 'quote))
(define unquote? (^quote? 'unquote))
(define unquote-splicing? (^quote? 'unquote-splicing))

(define const?
  (let ((simple-sexprs-predicates
         (list boolean? char? number? string?)))
    (lambda (e)
      (or (ormap (lambda (p?) (p? e))
                 simple-sexprs-predicates)
          (quote? e)))))

(define quotify
  (lambda (e)
    (if (or (null? e)
            (pair? e)
            (symbol? e)
            (vector? e))
        `',e
        e)))

(define unquotify
  (lambda (e)
    (if (quote? e)
        (cadr e)
        e)))

(define const-pair?
  (lambda (e)
    (and (quote? e)
         (pair? (cadr e)))))

(define expand-qq
  (letrec ((expand-qq
            (lambda (e)
              (cond ((unquote? e) (cadr e))
                    ((unquote-splicing? e)
                     (error 'expand-qq
                            "unquote-splicing here makes no sense!"))
                    ((pair? e)
                     (let ((a (car e))
                           (b (cdr e)))
                       (cond ((unquote-splicing? a)
                              `(append ,(cadr a) ,(expand-qq b)))
                             ((unquote-splicing? b)
                              `(cons ,(expand-qq a) ,(cadr b)))
                             (else `(cons ,(expand-qq a) ,(expand-qq b))))))
                    ((vector? e) `(list->vector ,(expand-qq (vector->list e))))
                    ((or (null? e) (symbol? e)) `',e)
                    (else e))))
           (optimize-qq-expansion (lambda (e) (optimizer e (lambda () e))))
           (optimizer
            (compose-patterns
             (pattern-rule
              `(append ,(? 'e) '())
              (lambda (e) (optimize-qq-expansion e)))
             (pattern-rule
              `(append ,(? 'c1 const-pair?) (cons ,(? 'c2 const?) ,(? 'e)))
              (lambda (c1 c2 e)
                (let ((c (quotify `(,@(unquotify c1) ,(unquotify c2))))
                      (e (optimize-qq-expansion e)))
                  (optimize-qq-expansion `(append ,c ,e)))))
             (pattern-rule
              `(append ,(? 'c1 const-pair?) ,(? 'c2 const-pair?))
              (lambda (c1 c2)
                (let ((c (quotify (append (unquotify c1) (unquotify c2)))))
                  c)))
             (pattern-rule
              `(append ,(? 'e1) ,(? 'e2))
              (lambda (e1 e2)
                (let ((e1 (optimize-qq-expansion e1))
                      (e2 (optimize-qq-expansion e2)))
                  `(append ,e1 ,e2))))
             (pattern-rule
              `(cons ,(? 'c1 const?) (cons ,(? 'c2 const?) ,(? 'e)))
              (lambda (c1 c2 e)
                (let ((c (quotify (list (unquotify c1) (unquotify c2))))
                      (e (optimize-qq-expansion e)))
                  (optimize-qq-expansion `(append ,c ,e)))))
             (pattern-rule
              `(cons ,(? 'e1) ,(? 'e2))
              (lambda (e1 e2)
                (let ((e1 (optimize-qq-expansion e1))
                      (e2 (optimize-qq-expansion e2)))
                  (if (and (const? e1) (const? e2))
                      (quotify (cons (unquotify e1) (unquotify e2)))
                      `(cons ,e1 ,e2))))))))
    (lambda (e)
      (optimize-qq-expansion
       (expand-qq e)))))



;------------------------------------------------------------------------------------------------------
(define void-object
  (if #f #f))

;-------var----
(define *reserved-words*
  '(and begin cond define do else if lambda
        let let* letrec or quasiquote unquote
        unquote-splicing quote set!))

(define reserved-word?
  (lambda (v) (ormap (lambda (x) (equal? v x)) *reserved-words*)
    ))

(define var?
  (lambda (v)
    (and (symbol? v) (not (reserved-word? v)))
    ))


;-----seq-----
(define seq-delete
  (lambda (seq)
    (if (null? seq) seq
        (if (equal? 'seq (car seq)) (seq-delete (cdr seq))
            (if (pair? (car seq)) (append (seq-delete (car seq)) (seq-delete (cdr seq)))
                 (list (car seq) (list (seq-delete (cdr seq)))))))))

(define pre-seq-delete
  (lambda (seq)
    (if (equal? 'seq (caadr seq)) `(seq ,@(seq-delete (cdr seq)))
        `(seq ,(seq-delete (cdr seq))))))
    




(define identify-lambda
  (lambda (argl ret-simple ret-opt ret-var)
    (cond 
      ((null? argl) (ret-simple '()))
      ((var? argl) (ret-var argl))     
      (else (identify-lambda (cdr argl)
                             (lambda (s) (ret-simple `(,(car argl) ,@s))) ;simple
                             (lambda (s opt) (ret-opt `(,(car argl) ,@s) opt)) ;opt
                             (lambda (var) (ret-opt `(,(car argl)) var)))))))



;---------------------------------------unbeginigy----------------------------------------


(define beginify
	(lambda (s)
		(cond
			((null? s) *void-object*)
			((null? (cdr s)) (cdr s))
			(else `(begin ,@s)))))

(define unbeginify ;;original unbeginify
  (lambda (s)
    (if (null? s)
        s
        (if (pair? s)
            (if (list? (car s))
                (if (eqv? 'begin (caar s))
                    `(,@(unbeginify(list-tail (car s) 1)) ,@(unbeginify(cdr s)))
                    `(,(car s) ,@(unbeginify (cdr s))))
                `(,(car s) ,@(unbeginify (cdr s))))
            s))))

(define parse-2
  (let ((run
         (compose-patterns

          ;--------------------applications-----------implimented
          (pattern-rule
           `(,(? 'proc (lambda (x) (not (reserved-word? x)))) . ,(? 'args)) ;maybe should change to reserved-symbol??
           (lambda (proc args)
             `(applic ,(parse-2 proc) ,(map parse-2 args))))
          ;---------------------const---------------implimented 
          ;Nil---------------implimented
          (pattern-rule
           (? 'c null?)
           (lambda (c) `(const '())))

          ;void---------------implimented
          (pattern-rule
           (? 'c (lambda (x) (equal? x void-object)))
           (lambda (c) `(const ,c)))
          ;vector---------------implimented
          (pattern-rule
           (? 'c vector?)
           (lambda (c) `(const ,c)))

          ;quote---------------implimented
          (pattern-rule
           `(quote ,(? 'c))
           (lambda (c) `(const ,c)))

          ;Boolean--------------implimented
          (pattern-rule
           (? 'c boolean?)
           (lambda (c) `(const ,c)))

          ;---------------------char--------------implimented
          (pattern-rule
           (? 'c char?)
           (lambda (c) `(const ,c)))

          ;---------------------number--------------implimented
          (pattern-rule
           (? 'c number?)
           (lambda (c) `(const ,c)))

          ;---------------------string--------------implimented
          (pattern-rule
           (? 'c string?)
           (lambda (c) `(const ,c)))

          ;---------------------var-----------------implimented
          (pattern-rule
           (? 'v var?)
           (lambda (v) `(var ,v)))

          ;---------------------if-------------------implimented
          ;if2
          (pattern-rule
           `(if ,(? 'test) ,(? 'dit))
           (lambda (test dit)
             `(if3 ,(parse-2 test) ,(parse-2 dit) (const ,void-object))))
          ;if3
          (pattern-rule
           `(if ,(? 'test) ,(? 'dit) ,(? 'dif))
           (lambda (test dit dif)
             `(if3 ,(parse-2 test) ,(parse-2 dit) ,(parse-2 dif))))

          ;--------------------Disjunctions----------------implimented
          (pattern-rule
           `(or . ,(? 'exprs))
           (lambda (exprs)
             (if (> (length exprs) 1)
             `(or ,(map parse-2 exprs))
             (if (= (length exprs) 1)
             `,(parse-2 (car exprs))
             `,(parse-2 `#f))
             )))

          ;--------------------Lambda----------------implimented----daniel


          

          (pattern-rule
           `(lambda ,(? 'args ) . ,(? 'exprs))
           (lambda (args exprs)
             (if (> (length exprs) 1)  
                 (identify-lambda args
                                  (lambda (s) `(lambda-simple ,s (seq (,@(map parse-2 (unbeginify exprs))))))
                                  (lambda (s opt) `(lambda-opt ,s ,opt (seq (,@(map parse-2 (unbeginify exprs))))))
                                  (lambda (var) `(lambda-var ,var (seq (,@(map parse-2 (unbeginify exprs))))))
                                  )
                 (identify-lambda args
                                  (lambda (s) `(lambda-simple ,s ,(parse-2 (car exprs))))
                                  (lambda (s opt) `(lambda-opt ,s ,opt ,(parse-2 (car exprs))))
                                  (lambda (var) `(lambda-var ,var ,(parse-2 (car exprs)))))
                                  )))



           ;--------------------Define----------------implimented
           ;regular define
           (pattern-rule
            `(define ,(? 'v (lambda (x) (not (pair? x)))) ,(? 'e))
            (lambda (v e)
              `(def ,`(var ,v) ,(parse-2 e))))

           ;MIT-style define
           (pattern-rule
            `(define ,(? 'v pair?) . ,(? 'e))
            (lambda (v e)
              `(def ,`(var ,(car v)) ,(parse-2 (append `(lambda ,(cdr v)) e))))) ;Didn't test waiting for lambda


           ;--------------------Assignments----------------implimented
           (pattern-rule
            `(set! ,(? 'v) ,(? 'e))
            (lambda (v e)
              `(set ,`(var ,v) ,(parse-2 e))))




           ;--------------------Sequences-----------implimented
           (pattern-rule
            `(begin  . ,(? 'seqs))
            (lambda (seqs)
              (if (> (length seqs) 1)
                  `(seq ,(map parse-2 (unbeginify seqs)))
                  (if (= (length seqs) 1)
                      `,(parse-2 (car seqs))
                      `,(parse-2 `,void-object)))))



          
           ;---------------------let----------------implimented
           (pattern-rule
            `(let ,(? 'def) . ,(? 'body))
            (lambda (def body)
              (parse-2 `((lambda ,(map car def) ,@body) ,@(map cadr def)))))
          
           ;---------------------let*----------------implimented
           (pattern-rule
            `(let* ,(? 'def) . ,(? 'body))
            (lambda (def body)
              (cond 
                ((null? def) (parse-2 `((lambda () (begin ,@body)))))
                ((null? (cdr def)) (parse-2 `(,`(lambda (,(caar def)) (begin ,@body)) ,(cadar def))))
                (else (parse-2 `((lambda (,(caar def)) (let* ,(cdr def) ,@body)) ,(cadar def)))))))


           ;---------------------letrec----------------implimented
           (pattern-rule
            `(letrec ,(? 'def) . ,(? 'body))
            (letrec ((make-letrec (lambda (syms vals)
                                    (if (null? syms) syms
                                        (if (null? (cdr syms)) `((set! ,(car syms) ,(car vals)))
                                            `(,`(set! ,(car syms) ,(car vals)) ,@(make-letrec (cdr syms) (cdr vals))))))))
                (lambda (def body)
                  (parse-2 `((lambda ,(map car def) 
                               (begin ,@(make-letrec (map car def) (map cadr def)) ((lambda () ,@body)))) 
                               ,@(map (lambda (x) #f) def))))))

          
           ;---------------------and----------------implimented
           (pattern-rule
            `(and)
            (lambda ()
              (parse-2 #t)))
           (pattern-rule
            `(and ,(? 'con))
            (lambda (con)
              (parse-2 con)))
           (pattern-rule
            `(and ,(? 'con1) ,(? 'con2))
            (lambda (con1 con2)
              (parse-2 `(if ,con1 ,con2 #f))))
           (pattern-rule
            `(and . ,(? 'conses))
            (lambda (conses)
              `(if3 ,(parse-2 (car conses)) ,(parse-2 `(and ,@(cdr conses))) ,(parse-2 #f))))

        ;--------------------QQ------------------------------------

           (pattern-rule
            `(quasiquote . ,(? 'exprs ))
            (lambda (exprs)
              (parse-2 (expand-qq (car exprs)))
              ))
           

           ;---------------------cond----------------not implimented TODO: seq
           
           (pattern-rule
            `(cond ,(? 'onec (lambda (x) (andmap pair? x))))
            (lambda (onec)
              (set! first (car onec))
              (set! other (cdr onec))
              (cond
                ((and (pair? (car first)) (equal? 'else (caar first))) (parse-2 (cadar first)))
                ((equal? 'else (car first)) (parse-2 (cadr first)))
                ((or (not (pair? other)) (null? other)) (parse-2 `(if ,(car first) (begin ,@(cdr first)))))           
                (else  (parse-2 `(if ,(car first)  (begin ,@(cdr first)) ,(if (equal? 'else (caar other)) `(begin ,@(cdar other))
                                                                     `(cond ,other))))))))
           (pattern-rule
            `(cond ,(? 'first) . ,(? 'other))
            (lambda (first other)
              (cond
                ((and (pair? (car first)) (equal? 'else (caar first))) (parse-2 (cadar first)))
                ((equal? 'else (car first)) (parse-2 (cadr first)))
                ((or (not (pair? other)) (null? other)) (parse-2 `(if ,(car first) (begin ,@(cdr first)))))           
                (else  (parse-2 `(if ,(car first) (begin ,@(cdr first)) ,(if (equal? 'else (caar other)) `(begin ,@(cdar other))
                                                                     `(cond ,other))))))))
         

           )))
        (lambda (e)
          (run e
               (lambda ()
                 (error 'parse-2
                        (format 'yet e)))))))

