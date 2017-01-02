;;; qq.scm
;;; A naive, one-level quasiquote implementation + optimizations
;;;
;;; Programmer: Mayer Goldberg, 2016

(load "pattern-matcher.scm")


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

(define parse
  (let ((run
         (compose-patterns

          ;--------------------applications-----------implimented
          (pattern-rule
           `(,(? 'proc (lambda (x) (not (reserved-word? x)))) . ,(? 'args)) ;maybe should change to reserved-symbol??
           (lambda (proc args)
             `(applic ,(parse proc) ,(map parse args))))
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
             `(if3 ,(parse test) ,(parse dit) (const ,void-object))))
          ;if3
          (pattern-rule
           `(if ,(? 'test) ,(? 'dit) ,(? 'dif))
           (lambda (test dit dif)
             `(if3 ,(parse test) ,(parse dit) ,(parse dif))))

          ;--------------------Disjunctions----------------implimented
          (pattern-rule
           `(or . ,(? 'exprs))
           (lambda (exprs)
             (if (> (length exprs) 1)
             `(or ,(map parse exprs))
             (if (= (length exprs) 1)
             `,(parse (car exprs))
             `,(parse `#f))
             )))

 ;--------------------Lambda----------------implimented----daniel
;          (pattern-rule
;           `(lambda ,(? 'args ) . ,(? 'exprs))
;           (lambda (args exprs)
;             (if (> (length exprs) 1)  
;                 (identify-lambda args
;                                  (lambda (s) `(lambda-simple ,s (seq (,@(map parse (unbeginify exprs))))))
;                                  (lambda (s opt) `(lambda-opt ,s ,opt (seq (,@(map parse (unbeginify exprs))))))
;                                  (lambda (var) `(lambda-var ,var (seq (,@(map parse (unbeginify exprs))))))
;                                  )
;                 (identify-lambda args
;                                  (lambda (s) `(lambda-simple ,s ,(parse (car exprs))))
;                                  (lambda (s opt) `(lambda-opt ,s ,opt ,(parse (car exprs))))
;                                  (lambda (var) `(lambda-var ,var ,(parse (car exprs)))))
;                                  )))
;


 ;          --------------------Lambda-NEW---------------implimented----daniel
         
          (pattern-rule
           `(lambda ,(? 'args ) . ,(? 'exprs))
           (lambda (args exprs)
             (let*
                 (;(parsed 3)
                  (parsed `(,@(map parse (unbeginify exprs))))
                  (defs (split parsed (lambda (d e) d)))
                  (exps (split parsed (lambda (d e) e)))
                  (app `(applic
                         (lambda-simple
                          (,@(map cadadr defs))
                          (seq (,@(map (lambda (def) `(set ,(cadr def) ,@(cddr def))) defs)
                                ,@exps)))
                         (,@(map (lambda(x) '(const #f)) defs)))))
               
               ;)
;               (display '++)
;               (display defs)
;               (display '--)
;               (display exps)
               (if (= 0 (length defs))
                   (if (> (length exprs) 1)  
                       (identify-lambda args
                                        (lambda (s) `(lambda-simple ,s (seq ,parsed)))
                                        (lambda (s opt) `(lambda-opt ,s ,opt (seq ,parsed)))
                                        (lambda (var) `(lambda-var ,var (seq parsed))))
                       (identify-lambda args
                                        (lambda (s) `(lambda-simple ,s ,(parse (car exprs))))
                                        (lambda (s opt) `(lambda-opt ,s ,opt ,(parse (car exprs))))
                                        (lambda (var) `(lambda-var ,var ,(parse (car exprs))))))
                   (identify-lambda args
                                    (lambda (s) `(lambda-simple ,s ,app))
                                    (lambda (s opt) `(lambda-opt ,s ,opt ,app))
                                    (lambda (var) `(lambda-var ,var ,app)))))))


           ;--------------------Define----------------implimented
           ;regular define
           (pattern-rule
            `(define ,(? 'v (lambda (x) (not (pair? x)))) ,(? 'e))
            (lambda (v e)
              `(def ,`(var ,v) ,(parse e))))

           ;MIT-style define
           (pattern-rule
            `(define ,(? 'v pair?) . ,(? 'e))
            (lambda (v e)
              `(def ,`(var ,(car v)) ,(parse (append `(lambda ,(cdr v)) e))))) ;Didn't test waiting for lambda


           ;--------------------Assignments----------------implimented
           (pattern-rule
            `(set! ,(? 'v) ,(? 'e))
            (lambda (v e)
              `(set ,`(var ,v) ,(parse e))))




           ;--------------------Sequences-----------implimented
           (pattern-rule
            `(begin  . ,(? 'seqs))
            (lambda (seqs)
              (if (> (length seqs) 1)
                  `(seq ,(map parse (unbeginify seqs)))
                  (if (= (length seqs) 1)
                      `,(parse (car seqs))
                      `,(parse `,void-object)))))



          
           ;---------------------let----------------implimented
           (pattern-rule
            `(let ,(? 'def) . ,(? 'body))
            (lambda (def body)
              (parse `((lambda ,(map car def) ,@body) ,@(map cadr def)))))
          
           ;---------------------let*----------------implimented
           (pattern-rule
            `(let* ,(? 'def) . ,(? 'body))
            (lambda (def body)
              (cond 
                ((null? def) (parse `((lambda () (begin ,@body)))))
                ((null? (cdr def)) (parse `(,`(lambda (,(caar def)) (begin ,@body)) ,(cadar def))))
                (else (parse `((lambda (,(caar def)) (let* ,(cdr def) ,@body)) ,(cadar def)))))))


           ;---------------------letrec----------------implimented
           (pattern-rule
            `(letrec ,(? 'def) . ,(? 'body))
            (letrec ((make-letrec (lambda (syms vals)
                                    (if (null? syms) syms
                                        (if (null? (cdr syms)) `((set! ,(car syms) ,(car vals)))
                                            `(,`(set! ,(car syms) ,(car vals)) ,@(make-letrec (cdr syms) (cdr vals))))))))
                (lambda (def body)
                  (parse `((lambda ,(map car def) 
                               (begin ,@(make-letrec (map car def) (map cadr def)) ((lambda () ,@body)))) 
                               ,@(map (lambda (x) #f) def))))))

          
           ;---------------------and----------------implimented
           (pattern-rule
            `(and)
            (lambda ()
              (parse #t)))
           (pattern-rule
            `(and ,(? 'con))
            (lambda (con)
              (parse con)))
           (pattern-rule
            `(and ,(? 'con1) ,(? 'con2))
            (lambda (con1 con2)
              (parse `(if ,con1 ,con2 #f))))
           (pattern-rule
            `(and . ,(? 'conses))
            (lambda (conses)
              `(if3 ,(parse (car conses)) ,(parse `(and ,@(cdr conses))) ,(parse #f))))

        ;--------------------QQ------------------------------------

           (pattern-rule
            `(quasiquote . ,(? 'exprs ))
            (lambda (exprs)
              (parse (expand-qq (car exprs)))
              ))
           

           ;---------------------cond----------------not implimented TODO: seq
           
           (pattern-rule
            `(cond ,(? 'onec (lambda (x) (andmap pair? x))))
            (lambda (onec)
              (set! first (car onec))
              (set! other (cdr onec))
              (cond
                ((and (pair? (car first)) (equal? 'else (caar first))) (parse (cadar first)))
                ((equal? 'else (car first)) (parse (cadr first)))
                ((or (not (pair? other)) (null? other)) (parse `(if ,(car first) (begin ,@(cdr first)))))           
                (else  (parse `(if ,(car first)  (begin ,@(cdr first)) ,(if (equal? 'else (caar other)) `(begin ,@(cdar other))
                                                                     `(cond ,other))))))))
           (pattern-rule
            `(cond ,(? 'first) . ,(? 'other))
            (lambda (first other)
              (cond
                ((and (pair? (car first)) (equal? 'else (caar first))) (parse (cadar first)))
                ((equal? 'else (car first)) (parse (cadr first)))
                ((or (not (pair? other)) (null? other)) (parse `(if ,(car first) (begin ,@(cdr first)))))           
                (else  (parse `(if ,(car first) (begin ,@(cdr first)) ,(if (equal? 'else (caar other)) `(begin ,@(cdar other))
                                                                     `(cond ,other))))))))
         

           )))
        (lambda (e)
          (run e
               (lambda ()
                 (error 'parse
                        (format 'yet e)))))))

;-----------------------------------------------ass3------------------------------------------------------



;----------------------------------3 Eliminating nested define-expressions--------------------------------


(define letrecTest
  (lambda()
    (letrec
        ((id (lambda(x) x))
         (sq (lambda(x) (* x x))))
      (sq (id 2)))))

(define letrecTest2
  '(letrec
        ((id (lambda(x) x))
         (sq (lambda(x) (* x x))))
      (sq (id 2))))

(define split
  (lambda (pes ret-ds-es)
    (if (null? pes) (ret-ds-es '() '())
        (split
         (cdr pes)
         (lambda (ds es)
           (cond ((eq? (caar pes) 'def)
                  (ret-ds-es (cons (car pes) ds) es))
                 ((eq? (caar pes) 'seq)
                  (split (cadar pes)
                         (lambda (ds1 es1)
                           (ret-ds-es (append ds1 ds)
                                      (append es1 es)))))
                 (else (ret-ds-es ds (cons (car pes) es)))))))))

(define *test-expr*
  '(define my-even?
     (lambda (e)
       (define even? (lambda (n) (or (zero? n) (odd? (- n 1)))))
       (define odd?
         (lambda (n) (and (positive? n) (even? (- n 1)))))
       (even? e))))




; test
(define test2
  (lambda ()
    (split (parse test-expr2221)
           (lambda (d e) e))))

(define test222ex
  '(lambda(e)
     (define sq (lambda (x) (define y (lambda (z) (+ z 1))) (* x x (y 3))))
     (define id (lambda (x) x))
     (id (sq e))))

(define testlet
  '(letrec (
     (sq (lambda(z) (define y (lambda (z) (+ z 1))) (* x x (y 3))))
     (id (lambda(x) x)))
     (id (sq e))))
; test
(define test22
  (lambda () (split  `(,(parse test222ex))
                    (lambda (d e) e))))
(define test222
  (lambda () (split  `(,(parse test222ex))
                    (lambda (d e) d))))

(define square$
  (lambda (x cont) (cont (* x x))))
(define c
  (lambda (x) (lambda() 2 )))
                


;----------------------------------4 remove-applic-lambda-nil--------------------------------
(define nil-lambda?
  (lambda (e)
    (and (pair? e) (= 3 (length e)) (equal? 'lambda-simple (car e)) (null? (cadr e)))
    ))

(define remove-applic-lambda-nil
  (lambda (e)
    (cond ((or (not (pair? e)) (null? e)) e)
          ((and (equal? 'applic (car e)) (nil-lambda? (cadr e))) (remove-applic-lambda-nil (caddr (cadr e))))
          (else `(,(remove-applic-lambda-nil (car e)) ,@(remove-applic-lambda-nil (cdr e)))))
    ))

;---------------------------------5 Boxing of variables-----------------------------------------
;----finding boxing
(define deep-member-bound
  (lambda (var e)
    (cond ((equal? var e) #t)
          ((or (not (pair? e)) (null? e)) #f)
          ((member var e) #t)
          ((and (equal? 'lambda-simple (car e)) (member var (cadr e))) #f)
          ((and (equal? 'lambda-opt (car e)) (or (member var (cadr e)) (equal? var (caddr e)))) #f)
          ((and (equal? 'lambda-var (car e)) (equal? var (cadr e))) #f)
          (else (or (deep-member-bound var (car e)) (deep-member-bound var (cdr e)))))
    ))    


(define bounded?
  (lambda (e var)
    (cond ((or (not (pair? e)) (null? e)) #f)
          ((equal? 'lambda-simple (car e)) (and (deep-member-bound var (caddr e)) (not (member var (cadr e)))))
          ((equal? 'lambda-opt (car e)) (and (deep-member-bound var (cadddr e)) 
                                             (not (or (member var (cadr e)) (equal? var (caddr e))))))
          ((equal? 'lambda-var (car e)) (and (deep-member-bound var (caddr e)) (not (equal? var (cadr e)))))
          (else (or (bounded? (car e) var) (bounded? (cdr e) var))))
    ))


(define var-read?
  (lambda (e var)
    (cond ((equal? var e) #t)
          ((or (not (pair? e)) (null? e)) #f)
          ((equal? (car e) 'set) (var-read? (cddr e) var))
          ((and (equal? 'lambda-simple (car e)) (member var (cadr e))) #f)
          ((and (equal? 'lambda-opt (car e)) (or (member var (cadr e)) (equal? var (caddr e)))) #f)
          ((and (equal? 'lambda-var (car e)) (equal? var (cadr e))) #f)
          (else (or (var-read? (car e) var) (var-read? (cdr e) var))))
    ))


(define var-write?
  (lambda (e var)
    (cond ((or (not (pair? e)) (null? e)) #f)
          ((and (equal? 'lambda-simple (car e)) (member var (cadr e))) #f)
          ((and (equal? 'lambda-opt (car e)) (or (member var (cadr e)) (equal? var (caddr e)))) #f)
          ((and (equal? 'lambda-var (car e)) (equal? var (cadr e))) #f)
          ((and (equal? (car e) 'set) (equal? (cadadr e) var)) #t)
          (else (or (var-write? (car e) var) (var-write? (cdr e) var))))
    ))

(define should-box?
  (lambda (e var)
    (and (var-write? e var) (var-read? e var) (bounded? e var))
    ))

;------handaling boxing
(define make-boxes
  (lambda (to-box)
    (map (lambda (x) `(set (var ,x) (box (var ,x)))) to-box)
    ))

(define delete
  (lambda (original-list to-delete)
    (cond ((null? original-list) (list))
          ((equal? (car original-list) to-delete) (delete (cdr original-list) to-delete))
          (else (append (list (car original-list)) (delete (cdr original-list) to-delete))))
    ))

(define delete-elements
  (lambda (original-list to-delete)
    (if (null? to-delete) original-list
        (delete-elements (delete original-list (car to-delete)) (cdr to-delete)))
    ))

(define box-in-body
  (lambda (e list-vars)
    (cond ((or (not (pair? e)) (null? e) (null? list-vars)) e)
          ((and (equal? (car e) 'var) (member (cadr e) list-vars)) `(box-get ,e))
          ((and (equal? (car e) 'set) (equal? (caadr e) 'var) (member (cadadr e) list-vars)) 
           `(box-set ,(cadr e) ,@(box-in-body (cddr e) list-vars)))
          ((equal? 'lambda-simple (car e))  
           `(,(car e) ,(cadr e) ,(box-in-body (caddr e) (delete-elements list-vars (cadr e)))))
          ((equal? 'lambda-opt (car e))
           `(,(car e) ,(cadr e) ,(caddr e) ,(box-in-body (cadddr e) (delete-elements list-vars (cons (caddr e) (cadr e))))))
          ((equal? 'lambda-var (car e))  
           `(,(car e) ,(cadr e) ,(box-in-body (caddr e) (delete-elements list-vars (list (cadr e))))))
          (else `(,(box-in-body (car e) list-vars) ,@(box-in-body (cdr e) list-vars))))
    ))


(define box-vars-simple
  (lambda (e)
    (set! list-to-box (filter (lambda (x)  (should-box? (cddr e) x)) (cadr e)))
    `(,(make-boxes list-to-box) ,(box-in-body (cddr e) list-to-box))
    ))

(define box-vars-opt
  (lambda (e)
    (set! list-to-box (filter (lambda (x)  (should-box? (cdddr e) x)) (cons (caddr e) (cadr e))))
    `(,(make-boxes list-to-box) ,(box-in-body (cdddr e) list-to-box))
    ))

(define box-vars-var
  (lambda (e)
    (if (should-box? (cddr e) (cadr e))
        `(,(make-boxes (list (cadr e))) ,(box-in-body (cddr e) (list (cadr e))))
        '(()()))
    )) 
              
(define box-set
  (lambda (e)
    (cond ((or (not (pair? e)) (null? e)) e)
          ((and (equal? 'lambda-simple (car e)) (< 2 (length e)) (not (null? (car (box-vars-simple e)))))
           (begin (set! after-box-vars (box-vars-simple e))
                  `(,(car e) ,(cadr e) (seq (,@(car after-box-vars) ,@(if (equal? 'seq (caaadr after-box-vars))
                                                                               (box-set (cadar (cadr after-box-vars)))
                                                                               (box-set (cadr after-box-vars))))))
                  ))
          ((and (equal? 'lambda-opt (car e)) (< 2 (length e)) (not (null? (car (box-vars-opt e)))))
           (begin (set! after-box-vars (box-vars-opt e)) 
                  `(,(car e) ,(cadr e) ,(caddr e) (seq (,@(car after-box-vars) ,@(if (equal? 'seq (caaadr after-box-vars))
                                                                               (box-set (cadar (cadr after-box-vars)))
                                                                               (box-set (cadr after-box-vars))))))
                  ))
          ((and (equal? 'lambda-var (car e)) (< 2 (length e)) (not (null? (car (box-vars-var e)))))
           (begin (set! after-box-vars (box-vars-var e))
                  `(,(car e) ,(cadr e) (seq (,@(car after-box-vars) ,@(if (equal? 'seq (caaadr after-box-vars))
                                                                               (box-set (cadar (cadr after-box-vars)))
                                                                               (box-set (cadr after-box-vars))))))
                  ))
          (else `(,(box-set (car e)) ,@(box-set (cdr e)))))
    ))
       


;----------------------------6 Annotating Variables with their Lexical address---------------------
(define do-lex-bound
  (lambda (body var major minor)
    (cond ((or (not (pair? body)) (null? body)) body)
          ((and (equal? 'var (car body)) (equal? var (cadr body))) `(bvar ,(cadr body) ,major ,minor))
          ((equal? 'lambda-simple (car body)) (if (member var (cadr body)) body
                                    `(,(car body) ,(cadr body) ,@(do-lex-bound (cddr body) var (+ 1 major) minor))))
          ((equal? 'lambda-opt (car body)) (if (member var (cons (caddr body) (cadr body))) body
                                    `(,(car body) ,(cadr body) ,(caddr body) 
                                                  ,@(do-lex-bound (cdddr body) var (+ 1 major) minor))))
          ((equal? 'lambda-var (car body)) (if (equal? var (cadr body)) body
                                    `(,(car body) ,(cadr body) ,@(do-lex-bound (cddr body) var (+ 1 major) minor))))
          (else `(,(do-lex-bound (car body) var major minor) ,@(do-lex-bound (cdr body) var major minor))))
    ))

(define do-lex-parameter
  (lambda (body var minor)
    (cond ((or (not (pair? body)) (null? body)) body)
          ((and (equal? 'var (car body)) (equal? var (cadr body))) `(pvar ,(cadr body) ,minor))
          ((equal? 'lambda-simple (car body)) (if (member var (cadr body)) body
                                    `(,(car body) ,(cadr body) ,@(do-lex-bound (cddr body) var 0 minor))))
          ((equal? 'lambda-opt (car body)) (if (member var (cons (caddr body) (cadr body))) body
                                    `(,(car body) ,(cadr body) ,(caddr body)
                                                  ,@(do-lex-bound (cdddr body) var 0 minor))))
          ((equal? 'lambda-var (car body)) (if (equal? var (cadr body)) body
                                    `(,(car body) ,(cadr body) ,@(do-lex-bound (cddr body) var 0 minor))))
          (else `(,(do-lex-parameter (car body) var minor) ,@(do-lex-parameter (cdr body) var minor))))
    ))

(define do-lex
  (lambda (body vars minor)
    (if (null? vars) body
        (do-lex (do-lex-parameter body (car vars) minor) (cdr vars) (+ 1 minor)))
    ))

(define pe->lex-pe
  (lambda (e)
    (cond ((or (not (pair? e)) (null? e)) e)
          ((equal? 'var (car e)) `(fvar ,@(cdr e)))
          ((equal? 'lambda-simple (car e)) `(,(car e) ,(cadr e) ,(pe->lex-pe (do-lex (caddr e) (cadr e) 0))))
          ((equal? 'lambda-opt (car e)) 
           `(,(car e) ,(cadr e) ,(caddr e) ,(pe->lex-pe (do-lex (cadddr e) `(,@(cadr e) ,(caddr e)) 0))))
          ((equal? 'lambda-var (car e)) `(,(car e) ,(cadr e) ,(pe->lex-pe (do-lex (caddr e) (list (cadr e)) 0))))
          (else `(,(pe->lex-pe (car e)) ,@(pe->lex-pe (cdr e)))))
    ))

;-------------------------------7  Annotating tail calls----------------------------------------
(define prepare-seq-to-tail
  (lambda (e not-tail is-first?)
    (cond ((and is-first? (= 1 (length e))) `(,(list not-tail) ,e))
          ((null? (cdr e)) `(,not-tail ,e))
          (else (prepare-seq-to-tail (cdr e) (if is-first? `(,not-tail ,(car e)) `(,@not-tail ,(car e))) #f)))
    ))


(define annotate-tc 1)

(define annotate-tail
  (lambda (pe)
    (cond ((or (not (pair? pe)) (null? pe)) pe)
          ((equal? 'const (car pe)) pe)
          ((or (equal? 'var (car pe)) (equal? 'fvar (car pe)) (equal? 'pvar (car pe)) (equal? 'bvar (car pe))) pe)
          ((equal? 'lambda-simple (car pe)) `(,(car pe) ,(cadr pe) ,(annotate-tail (caddr pe))))
          ((equal? 'lambda-opt (car pe)) `(,(car pe) ,(cadr pe) ,(caddr pe) ,(annotate-tail (cadddr pe))))
          ((equal? 'lambda-var (car pe)) `(,(car pe) ,(cadr pe) ,(annotate-tail (caddr pe))))
          ((equal? 'if3 (car pe)) `(if3 ,(annotate-tc (cadr pe)) ,(annotate-tail (caddr pe)) ,(annotate-tail (cadddr pe))))
          ((equal? 'or (car pe)) `(or (,@(car (prepare-seq-to-tail (cdadr pe) (caadr pe) #t)) 
                                       ,@(annotate-tail (cadr (prepare-seq-to-tail (cdadr pe) (caadr pe) #t))))))
          ((or (equal? 'def (car pe)) (equal? 'define (car pe))) `(,(car pe) ,(cadr pe) ,(annotate-tc (caddr pe))))
          ((or (equal? 'box-set (car pe)) (equal? 'set (car pe))) `(,(car pe) ,(cadr pe) ,@(annotate-tc (cddr pe))))
          ((equal? 'box-get (car pe)) pe)
          ((equal? 'box (car pe)) `(box ,@(annotate-tc (cdr pe))))
          ((equal? 'applic (car pe)) `(tc-applic ,(annotate-tc (cadr pe)) ,(map annotate-tc (caddr pe))))
          ((equal? 'seq (car pe)) `(seq ,`(,@(map annotate-tc (car (prepare-seq-to-tail (cdadr pe) (caadr pe) #t)))
                                                 ,@(annotate-tail (cadr (prepare-seq-to-tail (cdadr pe) (caadr pe) #t))))))
          (else `(,(annotate-tail (car pe)))))
    ))


(define annotate-tc
  (lambda (pe)
    (cond ((or (not (pair? pe)) (null? pe)) pe)
          ((equal? 'const (car pe)) pe)
          ((or (equal? 'var (car pe)) (equal? 'fvar (car pe)) (equal? 'pvar (car pe)) (equal? 'bvar (car pe))) pe)
          ((equal? 'lambda-simple (car pe)) `(,(car pe) ,(cadr pe) ,(annotate-tail (caddr pe))))
          ((equal? 'lambda-opt (car pe)) `(,(car pe) ,(cadr pe) ,(caddr pe) ,(annotate-tail (cadddr pe))))
          ((equal? 'lambda-var (car pe)) `(,(car pe) ,(cadr pe) ,(annotate-tail (caddr pe))))
          ((equal? 'if3 (car pe)) `(if3 ,(annotate-tc (cadr pe)) ,(annotate-tc (caddr pe)) ,(annotate-tc (cadddr pe))))
          ((equal? 'or (car pe)) `(or (,@(car (prepare-seq-to-tail (cdadr pe) (caadr pe) #t)) 
                                       ,@(annotate-tc (cadr (prepare-seq-to-tail (cdadr pe) (caadr pe) #t))))))
          ((or (equal? 'def (car pe)) (equal? 'define (car pe))) `(,(car pe) ,(cadr pe) ,(annotate-tc (caddr pe))))
          ((or  (equal? 'box-set (car pe)) (equal? 'set (car pe))) `(,(car pe) ,(cadr pe) ,@(annotate-tc (cddr pe))))
          ((equal? 'box-get (car pe)) pe)
          ((equal? 'box (car pe)) `(box ,@(annotate-tc (cdr pe))))
          ((equal? 'applic (car pe)) `(applic ,(annotate-tc (cadr pe)) ,(map annotate-tc (caddr pe))))
          ((equal? 'seq (car pe)) `(seq ,(map annotate-tc (cadr pe))))
          (else `(,(annotate-tc (car pe)))))
    ))   
