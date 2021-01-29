;{{{ Macro
(define-syntax defopt
  (syntax-rules ()
    [(_ (p x ... [y e]) b1 b2 ...)
     (define p
       (case-lambda
         [(x ...) (p x ... e)]
         [(x ... y) b1 b2 ...]))]))
;}}}

;{{{ Red-Black Tree
(module rbt%
    (rbt-node rbt-show rbt-search
     rbt-insert! rbt-delete! list->rbt)
;{{{ Macro
(define-syntax with-set@
  (lambda (x)
    (syntax-case x ()
      [(name body ...)
       (datum->syntax #'name (syntax->datum
         #'(if (eq? car@ car)
             (let ([set-car@! set-car!]
                   [set-cdr@! set-cdr!])
               body ...)
             (let ([set-car@! set-cdr!]
                   [set-cdr@! set-car!])
               body ...))))])))

(define-syntax make-son
  (syntax-rules ()
    [(_ (f p n) ...)
     (begin
       (let ([p& p] [n& n])
         (f (cddr p&) n&)
         (set-cdr! (car n&) p&))
       ...)]))

(define-syntax make-adoption
  (syntax-rules ()
    [(_ rbt n1 n2)
     (let* ([n1& n1] [n2& n2]
            [p (cdar n1&)])
       (set-cdr! (car n2&) p)
       (if (pair? (car p))
         ((if (eq? n1& (caddr p))
            set-car! set-cdr!)
          (cddr p) n2&)
         (set! rbt n2&)))]))
;}}}

;{{{ New tree/node
(defopt (rbt-node [p (cons = <)])
  (list (cons 'b p)))
;}}}
;{{{ Print tree
(defopt (rbt-show rbt [tab '(1 3 1)])
  (let* ([h #\x2500] [v #\x2502] [u #\x250c] [d #\x2514]
         ;[h #\-] [v #\|] [u #\/] [d #\\]
         [s #\space] [str "~a\x1b;[3~d;1m~a\x1b;[m~%"] [black 0] [red 1]
         [nps (car tab)] [ns (cadr tab)] [nss (caddr tab)]
         [sp (make-string (+ nps ns nss) s)] [hh (make-string (1- ns) h)]
         [ps (make-string nps s)] [ss (make-string nss s)]
         [uh (string-append ps (make-string 1 u) hh ss)]
         [dh (string-append ps (make-string 1 d) hh ss)]
         [vs (string-append ps (make-string 1 v) (make-string (1- ns) s) ss)])
    (let loop ([st rbt] [lsp ps] [csp ps] [rsp ps])
      (unless (null? (cdr st))
        (loop (caddr st)
              (string-append lsp sp)
              (string-append lsp uh)
              (string-append lsp vs))
        (printf str csp (if (eq? (caar st) 'r) red black) (cadr st))
        (loop (cdddr st)
              (string-append rsp vs)
              (string-append rsp dh)
              (string-append rsp sp))))))
;}}}
;{{{ Search for element
(define (rbt-search rbt x)
  (let ([eql? (cadar rbt)] [lt? (cddar rbt)])
    (let loop ([st rbt])
      (cond [(or (null? (cdr st))
                 (eql? (cadr st) x)) st]
            [(lt? (cadr st) x) (loop (cdddr st))]
            [else (loop (caddr st))]))))
;}}}
;{{{ Adjust for red rule
(define ($rbt-adjust-red! rbt n)
  (let loop ([n n])
    (let ([p (cdar n)])
      (when (pair? (car p))
        (set-car! (car n) 'r)
        (if (symbol=? (caar p) 'r)
          (let* ([g (cdar p)]
                 [cdr@ (if (eq? p (caddr g))
                         cdr car)]
                 [u (cdr@ (cddr g))])
            (set-car! (car p) 'b)
            (if (symbol=? (caar u) 'r)
              (begin
                (set-car! (car u) 'b)
                (loop g))
              (let ([car@ (if (eq? n (caddr p))
                            car cdr)])
                (set-car! (car n) 'b)
                (when (eq? car@ cdr@)
                  (set! car@ (if (eq? cdr@ cdr)
                               car cdr))
                  (let ([s (car@ (cddr n))])
                    (with-set@ (make-son
                      (set-car@! g n)
                      (set-car@! n p)
                      (set-cdr@! p s)))
                    (set! p n)))
                (let ([b (cdr@ (cddr p))])
                  (make-adoption rbt g p)
                  (with-set@ (make-son
                    (set-cdr@! p g)
                    (set-car@! g b))))
                (loop p))))))))
  rbt)
;}}}
;{{{ Adjust for black rule
(define ($rbt-adjust-black! rbt n)
  (let loop ([n n])
    (if (symbol=? (caar n) 'r)
      (set-car! (car n) 'b)
      (let ([p (cdar n)])
        (if (pair? (car p))
          (let* ([cdr@ (if (eq? n (caddr p))
                         cdr car)]
                 [car@ (if (eq? cdr@ cdr)
                         car cdr)]
                 [b (cdr@ (cddr p))])
            (if (symbol=? (caar b) 'r)
              (let ([s (car@ (cddr b))])
                (set-car! (car p) 'r)
                (set-car! (car b) 'b)
                (make-adoption rbt p b)
                (with-set@ (make-son
                  (set-car@! b p)
                  (set-cdr@! p s)))
                (set! b s)))
            (if (null? (cdr b))
              (loop p)
              (let ([l (car@ (cddr b))]
                    [r (cdr@ (cddr b))])
                (set-car! (car b) 'r)
                (if (and (symbol=? (caar l) 'r)
                         (symbol=? (caar r) 'b))
                  (let ([s (cdr@ (cddr l))])
                    (with-set@ (make-son
                      (set-cdr@! p l)
                      (set-cdr@! l b)
                      (set-car@! b s)))
                    (set! r b) (set! b l)
                    (set! l (car@ (cddr b)))))
                (if (symbol=? (caar r) 'r)
                  (begin
                    (set-car! (car b) (caar p))
                    (set-car! (car p) 'b)
                    (set-car! (car r) 'b)
                    (make-adoption rbt p b)
                    (with-set@ (make-son
                      (set-car@! b p)
                      (set-cdr@! p l))))
                  (loop p)))))
          (set! rbt n)))))
  rbt)
;}}}
;{{{ Insert element
(define (rbt-insert! rbt x)
  (let ([n (rbt-search rbt x)])
    (if (null? (cdr n))
      (begin
        (set-cdr! n (cons x
          (cons (rbt-node n) (rbt-node n))))
        ($rbt-adjust-red! rbt n))
      (begin
        (set-car! (cdr n) x)
        rbt))))
;}}}
;{{{ Delete element
(define (rbt-delete! rbt x)
  (let ([n (rbt-search rbt x)])
    (if (null? (cdr n)) rbt
      (begin
        (let loop ()
          (unless (and (null? (cdaddr n))
                       (null? (cddddr n)))
            (let ([m (cond
                [(null? (cdaddr n)) (cdddr n)]
                [(null? (cddddr n)) (caddr n)]
                [else (let loop ([m (cdddr n)])
                        (if (null? (cdaddr m))
                          m (loop (caddr m))))])])
              (set-car! (cdr n) (cadr m))
              (set! n m) (loop))))
        (set-cdr! n '())
        ($rbt-adjust-black! rbt n)))))
;}}}
;{{{ Make tree from list
(defopt (list->rbt l [op #f])
  (fold-left (lambda (x y) (rbt-insert! x y))
    (if op (rbt-node op) (rbt-node)) l))
;}}}
)
;}}}
;{{{ AVL Tree
(module avlt%
    (avlt-node avlt-show avlt-search
     avlt-insert! avlt-delete! list->avlt)
;{{{ Macro
(define-syntax with-set@
  (lambda (x)
    (syntax-case x ()
      [(name body ...)
       (datum->syntax #'name (syntax->datum
         #'(if (eq? car@ car)
             (let ([set-car@! set-car!]
                   [set-cdr@! set-cdr!])
               body ...)
             (let ([set-car@! set-cdr!]
                   [set-cdr@! set-car!])
               body ...))))])))

(define-syntax make-son
  (syntax-rules ()
    [(_ (f p n) ...)
     (begin
       (let ([p& p] [n& n])
         (f (cddr p&) n&)
         (set-cdr! (car n&) p&))
       ...)]))

(define-syntax make-adoption
  (syntax-rules ()
    [(_ avlt n1 n2)
     (let* ([n1& n1] [n2& n2]
            [p (cdar n1&)])
       (set-cdr! (car n2&) p)
       (if (pair? (car p))
         ((if (eq? n1& (caddr p))
            set-car! set-cdr!)
          (cddr p) n2&)
         (set! avlt n2&)))]))

(define-syntax make-revision
  (syntax-rules ()
    [(_ [n x] ...)
     (begin
       (let ([n& n] [x& x])
         (set-car! (car n&)
                   (+ (caar n&) x&)))
       ...)]))
;}}}

;{{{ New tree/node
(defopt (avlt-node [p (cons = <)])
  (list (cons 0 p)))
;}}}
;{{{ Print tree
(defopt (avlt-show avlt [tab '(1 3 1)])
  (let* ([h #\x2500] [v #\x2502] [u #\x250c] [d #\x2514]
         ;[h #\-] [v #\|] [u #\/] [d #\\]
         [s #\space] [str "~a\x1b;[3~d;1m~a\x1b;[m~%"]
         [nps (car tab)] [ns (cadr tab)] [nss (caddr tab)]
         [sp (make-string (+ nps ns nss) s)] [hh (make-string (1- ns) h)]
         [ps (make-string nps s)] [ss (make-string nss s)]
         [uh (string-append ps (make-string 1 u) hh ss)]
         [dh (string-append ps (make-string 1 d) hh ss)]
         [vs (string-append ps (make-string 1 v) (make-string (1- ns) s) ss)])
    (let loop ([st avlt] [lsp ps] [csp ps] [rsp ps])
      (unless (null? (cdr st))
        (loop (caddr st)
              (string-append lsp sp)
              (string-append lsp uh)
              (string-append lsp vs))
        (printf str csp
                (case (- (caar (caddr st)) (caar (cdddr st)))
                  [-1 1] [0 5] [1 4] [else 0])
                (cadr st))
        (loop (cdddr st)
              (string-append rsp vs)
              (string-append rsp dh)
              (string-append rsp sp))))))
;}}}
;{{{ Search for element
(define (avlt-search avlt x)
  (let ([eql? (cadar avlt)] [lt? (cddar avlt)])
    (let loop ([st avlt])
      (cond [(or (null? (cdr st))
                 (eql? (cadr st) x)) st]
            [(lt? (cadr st) x) (loop (cdddr st))]
            [else (loop (caddr st))]))))
;}}}
;{{{ Adjust for balance
(define ($avlt-adjust! avlt n)
  (let loop ([n n] [car@ car] [car@@ #f])
    (let* ([cdr@ (if (eq? car@ car) cdr car)]
           [lh (if (null? (cdr n)) -1
                 (caar (car@ (cddr n))))]
           [rh (if (null? (cdr n)) -1
                 (caar (cdr@ (cddr n))))]
           [diff (- lh rh)] [r #f])
      (cond
        [(> diff 1)
         (let* ([s (car@ (cddr n))]
                [g (cdr@ (cddr s))])
           (if (eq? car@ car@@)
             (begin
               (make-adoption avlt n s)
               (with-set@ (make-son
                 (set-cdr@! s n)
                 (set-car@! n g)))
               (make-revision [n -1]))
             (let* ([p (car@ (cddr g))]
                    [u (cdr@ (cddr g))])
               (make-adoption avlt n g)
               (with-set@ (make-son
                 (set-car@! g s)
                 (set-cdr@! s p)
                 (set-cdr@! g n)
                 (set-car@! n u)))
               (make-revision
                 [n -1] [s -1] [g 1]))))]
        [(< diff -1)
         (let* ([g (cdr@ (cddr n))]
                [p (car@ (cddr g))]
                [u (cdr@ (cddr g))])
           (if (> (caar p) (caar u))
             (let* ([s (car@ (cddr p))]
                    [b (cdr@ (cddr p))])
               (make-adoption avlt n p)
               (with-set@ (make-son
                 (set-car@! p n)
                 (set-cdr@! n s)
                 (set-cdr@! p g)
                 (set-car@! g b)))
               (make-revision
                 [n -2] [g -1] [p 1])
               (set! r p))
             (begin
               (make-adoption avlt n g)
               (with-set@ (make-son
                 (set-car@! g n)
                 (set-cdr@! n p)))
               (if (< (caar p) (caar u))
                 (begin
                   (make-revision [n -2])
                   (set! r g))
                 (make-revision
                   [n -1] [g 1])))))]
        [else
         (let ([newh (if (null? (cdr n)) 0
                       (1+ (max lh rh)))])
           (unless (= (caar n) newh)
             (set-car! (car n) newh)
             (set! r n)))])
      (if r
        (let ([p (cdar r)])
          (if (pair? (car p))
            (loop p (if (eq? r (caddr p))
                      car cdr) car@))))))
  avlt)
;}}}
;{{{ Insert element
(define (avlt-insert! avlt x)
  (let ([n (avlt-search avlt x)])
    (if (null? (cdr n))
      (begin
        (set-cdr! n (cons x
          (cons (avlt-node n) (avlt-node n))))
        ($avlt-adjust! avlt n))
      (begin
        (set-car! (cdr n) x)
        avlt))))
;}}}
;{{{ Delete element
(define (avlt-delete! avlt x)
  (let ([n (avlt-search avlt x)])
    (if (null? (cdr n)) avlt
      (begin
        (let loop ()
          (unless (and (null? (cdaddr n))
                       (null? (cddddr n)))
            (let ([m (cond
                [(null? (cdaddr n)) (cdddr n)]
                [(null? (cddddr n)) (caddr n)]
                [else (let loop ([m (cdddr n)])
                        (if (null? (cdaddr m))
                          m (loop (caddr m))))])])
              (set-car! (cdr n) (cadr m))
              (set! n m) (loop))))
        (set-cdr! n '())
        ($avlt-adjust! avlt n)))))
;}}}
;{{{ Make tree from list
(defopt (list->avlt l [op #f])
  (fold-left (lambda (x y) (avlt-insert! x y))
    (if op (avlt-node op) (avlt-node)) l))
;}}}
)
;}}}
;{{{ B Tree
(module bt%
    (bt-node bt-show bt-search
     bt-insert! bt-delete! list->bt)
;{{{ New tree/node
(defopt (bt-node n [p (cons = <)])
  (if (or (not (integer? n)) (< n 2))
    (error 'bt-node
           (format "Invalid B-tree argument ~d" n))
    (list (cons (if (procedure? (car p)) (cons n p) p)
                (cons 0 (make-vector n))))))
;}}}
;{{{ Print tree
(defopt (bt-show bt [tab '(1 5)])
  (let* ([h #\x2500] [v #\x2503] [u #\x250e] [d #\x2516]
         [r #\x2520] [uv #\x2530] [dv #\x2538]
         ;[h #\-] [v #\|] [u #\/] [d #\\] [r #\|] [uv #\-] [dv #\-]
         [s #\space] [str "~a\x1b;[1m~a\x1b;[m~%"]
         [ns (cadr tab)] [ps (make-string (car tab) s)]
         [hh (make-string (1- ns) h)] [ss (make-string (1- ns) s)]
         [uh (string-append (make-string 1 u) hh)]
         [dh (string-append (make-string 1 d) hh)]
         [rh (string-append (make-string 1 r) hh)]
         [uvh (string-append (make-string 1 uv) hh)]
         [dvh (string-append (make-string 1 dv) hh)]
         [vs (string-append (make-string 1 v) ss)])
    (let loop ([st bt] [lsp ps] [csp ps] [rsp ps] [ssp ps])
      (let ([n (cadar st)] [table (cddar st)])
        (if (null? (cdr st))
          (let count ([i 0] [sp (if (= n 1) ssp lsp)])
            (when (< i n)
              (printf str sp (vector-ref table i))
              (if (= i (- n 2))
                (count (1+ i) rsp)
                (count (1+ i) csp))))
          (let ([rtable (cdr st)]
                [nlsp (string-append lsp (if (pair? (caaar st))
                                           uvh uh))]
                [nsp (string-append csp rh)]
                [nrsp (string-append rsp (if (pair? (caaar st))
                                           dvh dh))]
                [ncsp (string-append csp vs)])
            (let count ([i 0] [nlsp nlsp])
              (when (< i n)
                (loop (vector-ref rtable i) nlsp ncsp nsp nlsp)
                (printf str csp (vector-ref table i))
                (count (1+ i) nsp)))
            (loop (vector-ref rtable n) nsp ncsp nrsp nrsp)))))))
;}}}
;{{{ Search for element
(define (bt-search bt x)
  (let ([eql? (cadaar bt)] [lt? (cddaar bt)])
    (let loop ([st bt])
      (let-values ([(found index)
          (let ([table (cddar st)])
            (let loop ([i (1- (cadar st))])
              (cond
                [(or (negative? i)
                     (lt? (vector-ref table i) x))
                 (values #f (1+ i))]
                [(eql? (vector-ref table i) x)
                 (values #t i)]
                [else (loop (1- i))])))])
        (if found (values st index)
          (if (null? (cdr st)) (values st #f)
            (loop (vector-ref (cdr st) index))))))))
;}}}
;{{{ Insert element
(define (bt-insert! bt x)
  (let-values ([(st i) (bt-search bt x)])
    (if i (vector-set! (cddar st) i x)
      (let ([n (caaar bt)] [lt? (cddaar bt)])
        (let loop ([st st] [x x] [lt #f] [rt #f])
          (let ([table (cddar st)])
            (if (< (cadar st) n)
              (let ([k
                  (let loop ([i (1- (cadar st))])
                    (if (or (negative? i)
                            (lt? (vector-ref table i) x))
                      (begin
                        (vector-set! table (1+ i) x) (1+ i))
                      (begin
                        (vector-set! table (1+ i)
                                     (vector-ref table i))
                        (loop (1- i)))))])
                (unless (null? (cdr st))
                  (let ([table (cdr st)])
                    (let loop ([i (cadar st)])
                      (if (<= i k)
                        (begin
                          (vector-set! table k lt)
                          (vector-set! table (1+ k) rt))
                        (begin
                          (vector-set! table (1+ i)
                                       (vector-ref table i))
                          (loop (1- i)))))))
                (set-car! (cdar st) (1+ (cadar st))))
              (let ([h (quotient n 2)] [c #f] [k #f]
                    [nt (bt-node n (caar st))])
                (let ([rtable (cddar nt)] [inserted #f])
                  (let loop ([i (1- h)] [j (1- n)])
                    (if (negative? i)
                      (if (not inserted)
                        (if (lt? (vector-ref table j) x)
                          (begin
                            (set! c x)
                            (set! k (1+ j)))
                          (begin
                            (set! c (vector-ref table j))
                            (set! rtable table)
                            (loop j (1- j))))
                        (set! c (vector-ref table j)))
                      (if (and (not inserted)
                               (or (negative? j)
                                   (lt? (vector-ref table j) x)))
                        (begin
                          (vector-set! rtable i x)
                          (set! inserted #t)
                          (set! k (1+ j))
                          (if (not c)
                            (loop (1- i) j)))
                        (begin
                          (vector-set! rtable i
                                       (vector-ref table j))
                          (loop (1- i) (1- j)))))))
                (unless (null? (cdr st))
                  (set-cdr! nt (make-vector (1+ n)))
                  (let ([table (cdr st)] [rtable (cdr nt)]
                        [insert (list rt lt)] [c #f])
                    (let loop ([i h] [j n])
                      (if (negative? i)
                        (unless (null? insert)
                          (set! c #t)
                          (set! rtable table)
                          (loop (1+ j) j))
                        (if (and (not (null? insert)) (<= j k))
                          (if (= j k)
                            (begin
                              (unless c
                                (set-car! (car rt) nt)
                                (if (positive? i)
                                  (set-car! (car lt) nt)))
                              (loop i (1- k)))
                            (begin
                              (vector-set! rtable i (car insert))
                              (set! insert (cdr insert))
                              (loop (1- i) j)))
                          (unless (and c (null? insert))
                            (vector-set! rtable i
                                         (vector-ref table j))
                            (unless c
                              (set-car! (car (vector-ref rtable i)) nt))
                            (loop (1- i) (1- j))))))))
                (set-car! (cdar st) (- n h))
                (set-car! (cdar nt) h)
                (unless (pair? (caaar st))
                  (set! bt (bt-node n (caar st)))
                  (set-cdr! bt (make-vector (1+ n)))
                  (set-car! (car st) bt)
                  (set-car! (car nt) bt))
                (loop (caar st) c st nt))))))))
  bt)
;}}}
;{{{ Delete element
(define (bt-delete! bt x)
  (let-values ([(st i) (bt-search bt x)])
    (when i
      (unless (null? (cdr st))
        (let loop ([nd (vector-ref (cdr st) i)])
          (let ([j (cadar nd)])
            (if (null? (cdr nd))
              (let ([j (1- j)])
                (vector-set! (cddar st) i (vector-ref (cddar nd) j))
                (set! st nd) (set! i j))
              (loop (vector-ref (cdr nd) j))))))
      (let* ([n (caaar bt)] [h (quotient n 2)])
        (let loop ([st st] [q i])
          (let ([table (cddar st)])
            (if (or (> (cadar st) h) (not (pair? (caaar st))))
              (let ([m (cadar st)])
                (let loop ([i q] [j (1+ q)])
                  (when (< j m)
                    (vector-set! table i (vector-ref table j))
                    (loop j (1+ j))))
                (unless (null? (cdr st))
                  (let ([table (cdr st)])
                    (let loop ([i (1+ q)] [j (+ q 2)])
                      (when (< i m)
                        (vector-set! table i (vector-ref table j))
                        (loop j (1+ j))))))
                (set-car! (cdar st) (1- m))
                (when (and (zero? (cadar st)) (not (null? (cdr st))))
                  (set! bt (vector-ref (cdr st) 0))
                  (set-car! (car bt) (caar st))))
              (let* ([p (caar st)] [prtable (cdr p)] [k
                  (let loop ([i (cadar p)])
                    (if (or (negative? i) (eq? (vector-ref prtable i) st))
                      i (loop (1- i))))]
                  [lt (if (positive? k) (vector-ref prtable (1- k)) #f)]
                  [rt (if (< k (cadar p)) (vector-ref prtable (1+ k)) #f)])
                (cond
                  [(and lt (> (cadar lt) h))
                   (let ([ptable (cddar p)] [m (1- (cadar lt))] [k (1- k)])
                     (let loop ([i q] [j (1- q)])
                       (when (positive? i)
                         (vector-set! table i (vector-ref table j))
                         (loop j (1- j))))
                     (vector-set! table 0 (vector-ref ptable k))
                     (vector-set! ptable k (vector-ref (cddar lt) m))
                     (unless (null? (cdr st))
                       (let ([table (cdr st)])
                         (let loop ([i (1+ q)] [j q])
                           (when (positive? i)
                             (vector-set! table i (vector-ref table j))
                             (loop j (1- j))))
                         (vector-set! table 0 (vector-ref (cdr lt) (cadar lt)))
                         (set-car! (car (vector-ref table 0)) st)))
                     (set-car! (cdar lt) m))]
                  [(and rt (> (cadar rt) h))
                   (let ([ptable (cddar p)] [rtable (cddar rt)] [r (cadar rt)])
                     (let loop ([i q] [j (1+ q)])
                       (when (< j h)
                         (vector-set! table i (vector-ref table j))
                         (loop j (1+ j))))
                     (vector-set! table (1- h) (vector-ref ptable k))
                     (vector-set! ptable k (vector-ref rtable 0))
                     (let loop ([i 0] [j 1])
                       (when (< j r)
                         (vector-set! rtable i (vector-ref rtable j))
                         (loop j (1+ j))))
                     (unless (null? (cdr st))
                       (let ([table (cdr st)] [rtable (cdr rt)])
                         (let loop ([i (1+ q)] [j (+ q 2)])
                           (when (< i h)
                             (vector-set! table i (vector-ref table j))
                             (loop j (1+ j))))
                         (vector-set! table h (vector-ref rtable 0))
                         (set-car! (car (vector-ref table h)) st)
                         (let loop ([i 0] [j 1])
                           (when (< i r)
                             (vector-set! rtable i (vector-ref rtable j))
                             (loop j (1+ j))))))
                     (set-car! (cdar rt) (1- r)))]
                  [lt
                   (let ([ltable (cddar lt)])
                     (vector-set! ltable h (vector-ref (cddar p) (1- k)))
                     (let loop ([i (1+ h)] [j 0])
                       (when (< j h)
                         (if (= j q) (loop i (1+ j))
                           (begin
                             (vector-set! ltable i (vector-ref table j))
                             (loop (1+ i) (1+ j))))))
                     (unless (null? (cdr st))
                       (let ([table (cdr st)] [ltable (cdr lt)] [q (1+ q)])
                         (let loop ([i (1+ h)] [j 0])
                           (when (<= j h)
                             (if (= j q) (loop i (1+ j))
                               (begin
                                 (vector-set! ltable i (vector-ref table j))
                                 (set-car! (car (vector-ref ltable i)) lt)
                                 (loop (1+ i) (1+ j))))))))
                     (set-car! (cdar lt) (* h 2)))
                   (loop p (1- k))]
                  [rt
                   (let ([rtable (cddar rt)])
                     (let loop ([i q] [j (1+ q)])
                       (when (< j h)
                         (vector-set! table i (vector-ref table j))
                         (loop j (1+ j))))
                     (vector-set! table (1- h) (vector-ref (cddar p) k))
                     (let loop ([i h] [j 0])
                       (when (< j h)
                         (vector-set! table i (vector-ref rtable j))
                         (loop (1+ i) (1+ j))))
                     (unless (null? (cdr st))
                       (let ([table (cdr st)] [rtable (cdr rt)])
                         (let loop ([i (1+ q)] [j (+ q 2)])
                           (when (< i h)
                             (vector-set! table i (vector-ref table j))
                             (loop j (1+ j))))
                         (let loop ([i h] [j 0])
                           (when (<= j h)
                             (vector-set! table i (vector-ref rtable j))
                             (set-car! (car (vector-ref table i)) st)
                             (loop (1+ i) (1+ j))))))
                     (set-car! (cdar st) (* h 2)))
                   (loop p k)]))))))))
  bt)
;}}}
;{{{ Make tree from list
(defopt (list->bt l n [op #f])
  (fold-left (lambda (x y) (bt-insert! x y))
    (if op (bt-node n op) (bt-node n)) l))
;}}}
)
;}}}
;{{{ Treap
(module th%
    (th-node th-show th-search
     th-insert! th-delete! list->th)
;{{{ Macro
(define-syntax with-set@
  (lambda (x)
    (syntax-case x ()
      [(name body ...)
       (datum->syntax #'name (syntax->datum
         #'(if (eq? car@ car)
             (let ([set-car@! set-car!]
                   [set-cdr@! set-cdr!])
               body ...)
             (let ([set-car@! set-cdr!]
                   [set-cdr@! set-car!])
               body ...))))])))

(define-syntax make-son
  (syntax-rules ()
    [(_ (f p n) ...)
     (begin
       (let ([p& p] [n& n])
         (f (cddr p&) n&)
         (set-car! n& p&))
       ...)]))

(define-syntax make-adoption
  (syntax-rules ()
    [(_ th n1 n2)
     (let* ([n1& n1] [n2& n2]
            [p (car n1&)])
       (set-car! n2& p)
       (if (pair? (car p))
         ((if (eq? n1& (caddr p))
            set-car! set-cdr!)
          (cddr p) n2&)
         (set! th n2&)))]))
;}}}

;{{{ New tree/node
(defopt (th-node [p (cons = <)])
  (list p))
;}}}
;{{{ Print tree
(defopt (th-show th [tab '(1 3 1)])
  (let* ([h #\x2500] [v #\x2502] [u #\x250c] [d #\x2514]
         ;[h #\-] [v #\|] [u #\/] [d #\\]
         [s #\space] [str "~a\x1b;[38;5;2~d;1m~a\x1b;[m~%"]
         [nps (car tab)] [ns (cadr tab)] [nss (caddr tab)]
         [sp (make-string (+ nps ns nss) s)] [hh (make-string (1- ns) h)]
         [ps (make-string nps s)] [ss (make-string nss s)]
         [uh (string-append ps (make-string 1 u) hh ss)]
         [dh (string-append ps (make-string 1 d) hh ss)]
         [vs (string-append ps (make-string 1 v) (make-string (1- ns) s) ss)])
    (let loop ([st th] [lsp ps] [csp ps] [rsp ps])
      (unless (null? (cdr st))
        (loop (caddr st)
              (string-append lsp sp)
              (string-append lsp uh)
              (string-append lsp vs))
        (printf str csp
                (+ 31 (remainder (- 25 (exact (floor (* (cdadr st) 25)))) 25))
                (caadr st))
        (loop (cdddr st)
              (string-append rsp vs)
              (string-append rsp dh)
              (string-append rsp sp))))))
;}}}
;{{{ Search for element
(define (th-search th x)
  (let ([eql? (caar th)] [lt? (cdar th)])
    (let loop ([st th])
      (cond [(or (null? (cdr st))
                 (eql? (caadr st) x)) st]
            [(lt? (caadr st) x) (loop (cdddr st))]
            [else (loop (caddr st))]))))
;}}}
;{{{ Insert element
(define (th-insert! th x)
  (let ([n (th-search th x)])
    (if (null? (cdr n))
      (begin
        (set-cdr! n (cons
          (cons x (random 1.))
          (cons (th-node n) (th-node n))))
        (let loop ()
          (let ([p (car n)])
            (when (and (pair? (car p))
                       (< (cdadr n) (cdadr p)))
              (let* ([car@ (if (eq? n (caddr p))
                             car cdr)]
                     [cdr@ (if (eq? car@ car)
                             cdr car)]
                     [s (cdr@ (cddr n))])
                (make-adoption th p n)
                (with-set@ (make-son
                  (set-cdr@! n p)
                  (set-car@! p s)))
                (loop))))))
      (begin
        (set-car! (cadr n) x)))
    th))
;}}}
;{{{ Delete element
(define (th-delete! th x)
  (let ([n (th-search th x)])
    (unless (null? (cdr n))
      (let loop ()
        (cond [(null? (cdaddr n))
               (make-adoption th n (cdddr n))]
              [(null? (cddddr n))
               (make-adoption th n (caddr n))]
              [else
               (let* ([car@ (if (< (cdadr (caddr n))
                                   (cdadr (cdddr n)))
                              car cdr)]
                      [cdr@ (if (eq? car@ car)
                              cdr car)]
                      [s (car@ (cddr n))]
                      [g (cdr@ (cddr s))])
                 (make-adoption th n s)
                 (with-set@ (make-son
                   (set-cdr@! s n)
                   (set-car@! n g)))
                 (loop))])))
    th))
;}}}
;{{{ Make tree from list
(defopt (list->th l [op #f])
  (fold-left (lambda (x y) (th-insert! x y))
    (if op (th-node op) (th-node)) l))
;}}}
)
;}}}
;{{{ Skiplist
(module sl%
    (sl-node sl-show sl-search
     sl-insert! sl-delete! list->sl)
;{{{ New list/node
(defopt (sl-node t [p (cons = <)])
  (if (and t (or (not (real? t)) (<= t 0) (> t 1)))
    (error 'sl-node
           (format "Invalid skiplist argument ~a" t))
    (if t
      (cons (cons 0 (cons t p)) (cons '() '()))
      (cons (car p) (cdr p)))))
;}}}
;{{{ Print list
(defopt (sl-show sl [tab '(1 3 1)])
  (let* ([h #\x2500] [l #\x25c0]
         ;[h #\-] [l #\<]
         [s #\space] [str "\x1b;[1m~a\x1b;[m~%"]
         [nps (car tab)] [ns (cadr tab)] [nss (caddr tab)]
         [ps (make-string nps s)]
         [la (string-append (make-string 1 l)
                            (make-string ns h)
                            (make-string nss s))])
    (let loop ([start sl] [end '()] [level (caar sl)])
      (let count ([last start] [node (cddr start)])
        (let ([last (cadr last)]
              [node (if (null? node) '() (cadr node))])
          (unless (null? last)
            (loop last node (1- level))))
        (unless (eq? node end)
          (display ps)
          (let loop ([i level])
            (when (positive? i)
              (display la)
              (loop (1- i))))
          (printf str (unbox (car node)))
          (count node (cddr node)))))))
;}}}
;{{{ Search for element
(define (sl-search sl x)
  (let ([eql? (caddar sl)] [lt? (cdddar sl)])
    (let loop ([last sl] [node (cddr sl)])
      (let* ([f (not (null? node))]
             [v (and f (unbox (car node)))])
        (cond [(and f (eql? v x)) (values v #t)]
              [(and f (lt? v x)) (loop node (cddr node))]
              [else
               (if (null? (cadr last)) (values #f #f)
                 (loop (cadr last) (cddadr last)))])))))

(define ($sl-trace sl x)
  (let ([eql? (caddar sl)] [lt? (cdddar sl)] [k #f])
    (let loop ([last sl] [node (cddr sl)] [l '()])
      (let* ([f (not (null? node))]
             [v (and f (unbox (car node)))])
        (if (and f (lt? v x)) (loop node (cddr node) l)
          (let ([last (cadr last)] [l
              (if (and (not k) f (eql? v x))
                (begin (set! k #t) (list last))
                (cons last l))])
            (if (null? last) (values l k)
              (loop last (cddr last) l))))))))
;}}}
;{{{ Insert element
(define (sl-insert! sl x)
  (let-values ([(l f) ($sl-trace sl x)])
    (if f (set-box! (caar l) x)
      (let* ([t (cadar sl)] [m (caar sl)]
             [n (let loop ([n 0])
                  (if (or (< (random 1.) t)
                          (> n m)) n
                    (loop (1+ n))))]
             [b (box x)])
        (cond
          [(> n m)
           (let ([meta (car sl)])
             (let loop ([n (- n m)]
                        [head sl] [ap '()])
               (if (positive? n)
                 (let ([new (sl-node #f
                         (list meta head))])
                   (loop (1- n) new (cons new ap)))
                 (begin
                   (set! sl head)
                   (append! l (reverse! ap)))))
             (set-car! (car sl) n))]
          [(< n m)
           (set-cdr! (list-tail l n) '())])
        (let loop ([l l] [head '()])
          (unless (null? l)
            (let* ([pre (cdar l)]
                   [new (sl-node #f
                     (list* b head (cdr pre)))])
              (set-cdr! pre new)
              (loop (cdr l) new)))))))
  sl)
;}}}
;{{{ Delete element
(define (sl-delete! sl x)
  (let-values ([(l f) ($sl-trace sl x)])
    (when f
      (let loop ([l l])
        (unless (null? l)
          (let* ([pre (cdar l)])
            (set-cdr! pre (cdddr pre))
            (loop (cdr l)))))
      (let loop ([node sl] [n (caar sl)])
        (let ([next (cadr node)])
          (if (and (null? (cddr node))
                   (not (null? next)))
            (loop next (1- n))
            (if (not (eq? node sl))
              (begin
                (set! sl node)
                (set-car! (car sl) n))))))))
  sl)
;}}}
;{{{ Make skiplist from list
(defopt (list->sl l t [op #f])
  (fold-left (lambda (x y) (sl-insert! x y))
    (if op (sl-node t op) (sl-node t)) l))
;}}}
)
;}}}
;{{{ Finite-Set Type
;{{{ Operations Based On Red-Black Tree
(module $fset-rbt%
    (fset $ds-tag make-fset fset?
     $fset-op $fset-copy fset-length fset->list
     fset-member fset-member? fset-adjoin! fset-remove!)
    (import rbt%) (define $ds-tag "rbt")
;{{{ Definition
(define-record-type (fset $make-fset fset?)
  (fields
    (mutable data))
  (nongenerative)
  (sealed #t))

(define make-fset
  (case-lambda
    [() ($make-fset (rbt-node))]
    [(l) ($make-fset (list->rbt l))]
    [(l op) ($make-fset (list->rbt l op))]))
;}}}
;{{{ Operations
(define ($fset-op s)
  (cdar (fset-data s)))

(define ($fset-copy s)
  ($make-fset
    (let loop ([n (fset-data s)] [p (cdar (fset-data s))])
      (if (null? (cdr n)) (list (cons (caar n) p))
        (let ([m (cons (cons (caar n) p)
                       (cons (cadr n) #f))])
          (set-cdr! (cdr m)
                    (cons (loop (caddr n) m)
                          (loop (cdddr n) m)))
          m)))))

(define (fset-length s)
  (let loop ([n (fset-data s)])
    (if (null? (cdr n)) 0
      (+ 1 (loop (caddr n))
           (loop (cdddr n))))))

(define (fset->list s)
  (let loop ([n (fset-data s)] [l '()])
    (if (null? (cdr n)) l
      (loop (caddr n)
            (cons (cadr n)
                  (loop (cdddr n) l))))))

(define (fset-adjoin! s x)
  (fset-data-set! s (rbt-insert! (fset-data s) x)))

(define (fset-remove! s x)
  (fset-data-set! s (rbt-delete! (fset-data s) x)))

(define (fset-member s x)
  (let ([n (rbt-search (fset-data s) x)])
    (if (null? (cdr n)) #f
      (cadr n))))

(define (fset-member? s x)
  (let ([n (rbt-search (fset-data s) x)])
    (not (null? (cdr n)))))
;}}}
)
;}}}
;{{{ Operations Based On AVL Tree
(module $fset-avlt%
    (fset $ds-tag make-fset fset?
     $fset-op $fset-copy fset-length fset->list
     fset-member fset-member? fset-adjoin! fset-remove!)
    (import avlt%) (define $ds-tag "avlt")
;{{{ Definition
(define-record-type (fset $make-fset fset?)
  (fields
    (mutable data))
  (nongenerative)
  (sealed #t))

(define make-fset
  (case-lambda
    [() ($make-fset (avlt-node))]
    [(l) ($make-fset (list->avlt l))]
    [(l op) ($make-fset (list->avlt l op))]))
;}}}
;{{{ Operations
(define ($fset-op s)
  (cdar (fset-data s)))

(define ($fset-copy s)
  ($make-fset
    (let loop ([n (fset-data s)] [p (cdar (fset-data s))])
      (if (null? (cdr n)) (list (cons (caar n) p))
        (let ([m (cons (cons (caar n) p)
                       (cons (cadr n) #f))])
          (set-cdr! (cdr m)
                    (cons (loop (caddr n) m)
                          (loop (cdddr n) m)))
          m)))))

(define (fset-length s)
  (let loop ([n (fset-data s)])
    (if (null? (cdr n)) 0
      (+ 1 (loop (caddr n))
           (loop (cdddr n))))))

(define (fset->list s)
  (let loop ([n (fset-data s)] [l '()])
    (if (null? (cdr n)) l
      (loop (caddr n)
            (cons (cadr n)
                  (loop (cdddr n) l))))))

(define (fset-adjoin! s x)
  (fset-data-set! s (avlt-insert! (fset-data s) x)))

(define (fset-remove! s x)
  (fset-data-set! s (avlt-delete! (fset-data s) x)))

(define (fset-member s x)
  (let ([n (avlt-search (fset-data s) x)])
    (if (null? (cdr n)) #f
      (cadr n))))

(define (fset-member? s x)
  (let ([n (avlt-search (fset-data s) x)])
    (not (null? (cdr n)))))
;}}}
)
;}}}
;{{{ Operations Based On B Tree
(module $fset-bt%
    (fset $ds-tag make-fset fset?
     $fset-op $fset-copy fset-length fset->list
     fset-member fset-member? fset-adjoin! fset-remove!)
    (import bt%) (define $ds-tag "bt")
;{{{ Definition
(define-record-type (fset $make-fset fset?)
  (fields
    (mutable data))
  (nongenerative)
  (sealed #t))

(define make-fset
  (case-lambda
    [() ($make-fset (bt-node))]
    [(l) ($make-fset (list->bt l 4))]
    [(l op) ($make-fset (list->bt l 4 op))]
    [(l op n) ($make-fset (list->bt l n op))]))
;}}}
;{{{ Operations
(define ($fset-op s)
  (cdaar (fset-data s)))

(define ($fset-copy s)
  ($make-fset
    (let loop ([n (fset-data s)] [p (caar (fset-data s))])
      (if (null? (cdr n))
        (list (cons p (cons (cadar n) (vector-copy (cddar n)))))
        (let* ([rtable (cdr n)]
               [mrtable (make-vector (vector-length rtable))]
               [m (cons (cons p (cons (cadar n)
                                      (vector-copy (cddar n))))
                        mrtable)])
          (let count ([i (cadar n)])
            (if (negative? i) m
              (begin
                (vector-set! mrtable i
                             (loop (vector-ref rtable i) m))
                (count (1- i))))))))))

(define (fset-length s)
  (let loop ([n (fset-data s)])
    (if (null? (cdr n)) (cadar n)
      (let ([rtable (cdr n)])
        (let count ([i (cadar n)])
          (if (negative? i) (cadar n)
            (+ (loop (vector-ref rtable i))
               (count (1- i)))))))))

(define (fset->list s)
  (let loop ([n (fset-data s)] [l '()])
    (let ([table (cddar n)] [rtable (cdr n)])
      (if (null? rtable)
        (let count ([i (1- (cadar n))] [l l])
          (if (negative? i) l
            (count (1- i) (cons (vector-ref table i) l))))
        (let count ([i (1- (cadar n))]
                    [l (loop (vector-ref rtable (cadar n)) l)])
          (if (negative? i) l
            (count (1- i)
              (loop (vector-ref rtable i)
                    (cons (vector-ref table i) l)))))))))

(define (fset-adjoin! s x)
  (fset-data-set! s (bt-insert! (fset-data s) x)))

(define (fset-remove! s x)
  (fset-data-set! s (bt-delete! (fset-data s) x)))

(define (fset-member s x)
  (let-values ([(n i) (bt-search (fset-data s) x)])
    (if i (vector-ref (cddar n) i) #f)))

(define (fset-member? s x)
  (let-values ([(n i) (bt-search (fset-data s) x)])
    (and i #t)))
;}}}
)
;}}}
;{{{ Operations Based On Treap
(module $fset-th%
    (fset $ds-tag make-fset fset?
     $fset-op $fset-copy fset-length fset->list
     fset-member fset-member? fset-adjoin! fset-remove!)
    (import th%) (define $ds-tag "th")
;{{{ Definition
(define-record-type (fset $make-fset fset?)
  (fields
    (mutable data))
  (nongenerative)
  (sealed #t))

(define make-fset
  (case-lambda
    [() ($make-fset (th-node))]
    [(l) ($make-fset (list->th l))]
    [(l op) ($make-fset (list->th l op))]))
;}}}
;{{{ Operations
(define ($fset-op s)
  (car (fset-data s)))

(define ($fset-copy s)
  ($make-fset
    (let loop ([n (fset-data s)] [p (car (fset-data s))])
      (if (null? (cdr n)) (list p)
        (let ([m (cons p (cons
                   (cons (caadr n) (cdadr n)) #f))])
          (set-cdr! (cdr m)
                    (cons (loop (caddr n) m)
                          (loop (cdddr n) m)))
          m)))))

(define (fset-length s)
  (let loop ([n (fset-data s)])
    (if (null? (cdr n)) 0
      (+ 1 (loop (caddr n))
           (loop (cdddr n))))))

(define (fset->list s)
  (let loop ([n (fset-data s)] [l '()])
    (if (null? (cdr n)) l
      (loop (caddr n)
            (cons (caadr n)
                  (loop (cdddr n) l))))))

(define (fset-adjoin! s x)
  (fset-data-set! s (th-insert! (fset-data s) x)))

(define (fset-remove! s x)
  (fset-data-set! s (th-delete! (fset-data s) x)))

(define (fset-member s x)
  (let ([n (th-search (fset-data s) x)])
    (if (null? (cdr n)) #f
      (caadr n))))

(define (fset-member? s x)
  (let ([n (th-search (fset-data s) x)])
    (not (null? (cdr n)))))
;}}}
)
;}}}
;{{{ Operations Based On Skiplist
(module $fset-sl%
    (fset $ds-tag make-fset fset?
     $fset-op $fset-copy fset-length fset->list
     fset-member fset-member? fset-adjoin! fset-remove!)
    (import sl%) (define $ds-tag "sl")
;{{{ Definition
(define-record-type (fset $make-fset fset?)
  (fields
    (mutable data))
  (nongenerative)
  (sealed #t))

(define make-fset
  (case-lambda
    [() ($make-fset (sl-node))]
    [(l) ($make-fset (list->sl l 1/2))]
    [(l op) ($make-fset (list->sl l 1/2 op))]
    [(l op t) ($make-fset (list->sl l t op))]))
;}}}
;{{{ Operations
(define ($fset-op s)
  (cddar (fset-data s)))

(define ($fset-copy s)
  (define-syntax cadr@
    (syntax-rules ()
      [(_ l)
       (if (null? l) '() (cadr l))]))
  ($make-fset
    (let loop ([a (fset-data s)] [b '()] [c '()])
      (let ([na (cddr a)] [da (cadr a)])
        (if (eq? na b)
          (if (null? da)
            (sl-node #f (list*
              (if (box? (car a))
                (box (unbox (car a)))
                (list* (caar a) (cadar a) (cddar a)))
              '() c))
            (let ([d (loop da (cadr@ b) (cadr@ c))])
              (sl-node #f (list* (car d) d c))))
          (loop a na (loop na b c)))))))

(define (fset-length s)
  (let loop ([n (cddr
      (let loop ([n (fset-data s)])
        (let ([nn (cadr n)])
          (if (null? nn) n
            (loop nn)))))])
    (if (null? n) 0
      (1+ (loop (cddr n))))))

(define (fset->list s)
  (let loop ([n (cddr
      (let loop ([n (fset-data s)])
        (let ([nn (cadr n)])
          (if (null? nn) n
            (loop nn)))))])
    (if (null? n) '()
      (cons (unbox (car n)) (loop (cddr n))))))

(define (fset-adjoin! s x)
  (fset-data-set! s (sl-insert! (fset-data s) x)))

(define (fset-remove! s x)
  (fset-data-set! s (sl-delete! (fset-data s) x)))

(define (fset-member s x)
  (let-values ([(n f) (sl-search (fset-data s) x)])
    n))

(define (fset-member? s x)
  (let-values ([(n f) (sl-search (fset-data s) x)])
    f))
;}}}
)
;}}}
;{{{ Data-Structure-Independent Operations
(module fset%
    (make-fset fset? fset-print-detail: fset-print-pretty:
     fset-op fset-copy fset-length fset->list
     fset-member fset-member? fset-adjoin! fset-remove!
     fset-union! fset-difference! fset-intersection!
     fset-adjoin fset-remove fset-union fset-difference fset-intersection
     fset-subset? fset-equal?)
    (import $fset-avlt%)
;{{{ Definition
(module ()
  (record-writer (type-descriptor fset)
    (lambda (x p wr)
      (if (fset-print-detail:)
        (if (fset-print-pretty:)
          (let ()
            ;{{{ Terminal Print Utilities
            #;(define ($fset->string s)
              (let* ([str (with-output-to-string
                            (lambda ()
                              (pretty-print
                                (cons (fset->list s) #t))))]
                     [n (let loop ([n (1- (string-length str))] [c 1])
                          (if (negative? n) -1
                            (if (char=? (string-ref str n) #\))
                              (if (zero? c) n
                                (loop (1- n) (1- c)))
                              (loop (1- n) c))))])
                (string-truncate! str (1+ n))
                (let loop ([m 0] [l '(" " "#{")])
                  (when (and (<= m n) (not (null? l)))
                    (when (char=? (string-ref str m) #\()
                      (let* ([s (car l)] [k (string-length s)])
                        (string-copy! s 0 str (1+ (- m k)) k))
                      (set! l (cdr l)))
                    (loop (1+ m) l)))
                (string-set! str n #\})
                str))

            (define ($fset->string s)
              (let* ([str (with-output-to-string
                            (lambda ()
                              (pretty-print
                                (list->vector (fset->list s)))))]
                     [n (let loop ([n (1- (string-length str))])
                          (if (negative? n) -1
                            (if (char=? (string-ref str n) #\)) n
                              (loop (1- n)))))])
                (string-truncate! str (1+ n))
                (let loop ([m 0])
                  (when (<= m n)
                    (if (char=? (string-ref str m) #\()
                      (string-set! str m #\{)
                      (loop (1+ m)))))
                (string-set! str n #\})
                str))
            
            (define ($string-split s c)
              (let ([n (string-length s)])
                (let loop ([n (1- n)] [e n] [l '()])
                  (if (negative? n) (cons (substring s 0 e) l)
                    (if (char=? (string-ref s n) c)
                      (loop (1- n) n (cons (substring s (1+ n) e) l))
                      (loop (1- n) e l))))))

            (define ($term-print-block l p)
              (let ([spos (lambda () (display "\x1b;[s" p))]
                    [lpos (lambda () (display "\x1b;[u" p))])
                (spos)
                (let loop ([l l] [tab ""])
                  (unless (null? l)
                    (lpos) (display tab p) (spos)
                    (format p "~a" (car l))
                    (loop (cdr l) #\vtab)))))
            ;}}}
            ($term-print-block
              ($string-split ($fset->string x) #\newline)
              p))
          (format p "#{~{~a~^ ~}}" (fset->list x)))
        (let ([pr ($fset-op x)])
          (format p "#<fset #[~a ~d ~a ~a]>"
                    $ds-tag (fset-length x)
                    (car pr) (cdr pr)))))))

(define fset-print-detail:
  (make-parameter #t (lambda (x) (and x #t))))

(define fset-print-pretty:
  (make-parameter #f (lambda (x) (and x #t))))
;}}}
;{{{ Operations
(define (fset-op s)
  (let ([op ($fset-op s)])
    (cons (car op) (cdr op))))

(define (fset-copy s)
  (make-fset (fset->list s) ($fset-op s)))

(define (fset-union! s . l)
  (let loop ([l l])
    (unless (null? l)
      (if (not (equal? ($fset-op s) ($fset-op (car l))))
        (error 'fset-union! "Incompatible fset type"))
      (for-each (lambda (x)
                  (fset-adjoin! s x))
                (fset->list (car l)))
      (loop (cdr l)))))

(define (fset-difference! s . l)
  (let loop ([l l])
    (unless (null? l)
      (if (not (equal? ($fset-op s) ($fset-op (car l))))
        (error 'fset-difference! "Incompatible fset type"))
      (for-each (lambda (x)
                  (fset-remove! s x))
                (fset->list (car l)))
      (loop (cdr l)))))

(define (fset-intersection! s . l)
  (let loop ([l l])
    (unless (null? l)
      (if (not (equal? ($fset-op s) ($fset-op (car l))))
        (error 'fset-intersection! "Incompatible fset type"))
      (for-each (lambda (x)
                  (fset-remove! s x))
                (filter (lambda (x)
                          (not (fset-member? (car l) x)))
                        (fset->list s)))
      (loop (cdr l)))))

(define (fset-adjoin s x)
  (let ([s ($fset-copy s)])
    (fset-adjoin! s x) s))

(define (fset-remove s x)
  (let ([s ($fset-copy s)])
    (fset-remove! s x) s))

(define (fset-union s . l)
  (let ([s ($fset-copy s)])
    (apply fset-union! (cons s l)) s))

(define (fset-difference s . l)
  (if (null? l) ($fset-copy s)
    (let* ([op ($fset-op s)] [eql? (car op)] [lt? (cdr op)])
      (make-fset
        (fold-right
          (lambda (x y)
            (let loop ([r '()] [s1 y] [s2 x])
              (if (or (null? s1) (null? s2))
                (append! (reverse! r) s1)
                (let ([x1 (car s1)] [x2 (car s2)])
                  (cond [(eql? x1 x2)
                         (loop r (cdr s1) (cdr s2))]
                        [(lt? x1 x2)
                         (loop (cons x1 r) (cdr s1) s2)]
                        [else
                         (loop r s1 (cdr s2))])))))
          (fset->list s)
          (let loop ([r '()] [l l])
            (if (null? l) r
              (begin
                (if (not (equal? op ($fset-op (car l))))
                  (error 'fset-difference "Incompatible fset type"))
                (loop (cons (fset->list (car l)) r) (cdr l))))))
        op))))

(define (fset-intersection s . l)
  (if (null? l) ($fset-copy s)
    (let* ([op ($fset-op s)] [eql? (car op)] [lt? (cdr op)])
      (make-fset
        (fold-right
          (lambda (x y)
            (let loop ([r '()] [s1 y] [s2 x])
              (if (or (null? s1) (null? s2)) (reverse! r)
                (let ([x1 (car s1)] [x2 (car s2)])
                  (cond [(eql? x1 x2)
                         (loop (cons x1 r) (cdr s1) (cdr s2))]
                        [(lt? x1 x2)
                         (loop r (cdr s1) s2)]
                        [else
                         (loop r s1 (cdr s2))])))))
          (fset->list s)
          (let loop ([r '()] [l l])
            (if (null? l) r
              (begin
                (if (not (equal? op ($fset-op (car l))))
                  (error 'fset-intersection "Incompatible fset type"))
                (loop (cons (fset->list (car l)) r) (cdr l))))))
        op))))

(define (fset-subset? s1 s2)
  (let* ([op ($fset-op s1)] [eql? (car op)] [lt? (cdr op)])
    (if (not (equal? op ($fset-op s2))) #f
      (let loop ([s1 (fset->list s1)] [s2 (fset->list s2)])
        (cond [(null? s1) #t]
              [(or (null? s2)
                   (lt? (car s1) (car s2))) #f]
              [else (loop (cdr s1)
                          (if (eql? (car s1) (car s2))
                            (cdr s2) s2))])))))

(define (fset-equal? s1 s2)
  (let* ([op ($fset-op s1)] [eql? (car op)])
    (if (not (equal? op ($fset-op s2))) #f
      (let loop ([s1 (fset->list s1)] [s2 (fset->list s2)])
        (cond [(and (null? s1) (null? s2)) #t]
              [(or (null? s1) (null? s2)
                   (not (eql? (car s1) (car s2)))) #f]
              [else (loop (cdr s1) (cdr s2))])))))
;}}}
)
;}}}
;}}}
;{{{ Test Utilities
(module (rbt-demo avlt-demo bt-demo th-demo sl-demo)
;{{{ Macro
(define-syntax with-demo
  (lambda (x)
    (syntax-case x ()
      [(_ body ...)
       (if (file-exists? "libdemo.so")
         #'(letrec
               ([demo-init (lambda () ((foreign-procedure "demo_init" () void)))]
                [demo-exit (lambda () ((foreign-procedure "demo_exit" () void)))]
                [iclean (lambda () (keyboard-interrupt-handler kbdi))]
                [isetup (lambda () (keyboard-interrupt-handler kbdi@))]
                [kbdi (keyboard-interrupt-handler)]
                [kbdi@ (lambda () (iclean) (kbdi) (demo-init) (isetup))])
             (load-shared-object "./libdemo.so")
             (isetup) (demo-init) body ... (demo-exit) (iclean))
         #'(begin (display "\x1b;[2J") body ...  (void)))])))

(define-syntax make-demo
  (lambda (x)
    (syntax-case x ()
      [(md name)
       (let* ([obj (syntax->datum #'name)]
              [argl (syntax->list (datum->syntax #'md
                      (if (pair? obj) (cdr obj) '())))]
              [prefix (symbol->string
                        (if (pair? obj) (car obj) obj))])
         (with-syntax
             ([% (datum->syntax #'md
                   (string->symbol
                     (string-append prefix "%")))]
              [fun
               (datum->syntax #'md
                 (string->symbol
                   (string-append prefix "-demo")))]
              [show
               (datum->syntax #'md
                 (string->symbol
                   (string-append prefix "-show")))]
              [insert!
               (datum->syntax #'md
                 (string->symbol
                   (string-append prefix "-insert!")))]
              [delete!
               (datum->syntax #'md
                 (string->symbol
                   (string-append prefix "-delete!")))]
              [node
               (datum->syntax #'md
                 (string->symbol
                   (string-append prefix "-node")))])
           #`(defopt (fun n [opt '(3 0.5)])
               (import %)
               (with-demo
                 (let* ([m (car opt)] [t (cadr opt)] [z (exact (floor t))]
                        [f (exact (floor (* (- t z) 1e9)))]
                        [l (let loop ([n n] [l '()])
                             (if (positive? n)
                               (loop (1- n) (cons n l)) l))]
                        [pre (lambda (x)
                               (display "\x1b;[1J\x1b;[H") (show x)
                               (sleep (make-time 'time-duration f z)) x)]
                        [gen (lambda (f)
                               (lambda (r l)
                                 (fold-left
                                   (lambda (x y)
                                     (pre (f x y))) r l)))]
                        [demo (let ([f #f]
                                    [ins (gen insert!)]
                                    [del (gen delete!)])
                                (lambda (x y)
                                  (set! f (not f))
                                  (if f (ins x y) (del x y))))])
                   (fold-left demo (node #,@argl)
                              (map shuffle (make-list m l))))))))]
      [(md name names ...)
       #'(begin
           (md name)
           (md names ...))])))
;}}}

(define (shuffle l)
  (let* ([n (length l)] [ind (make-vector n)])
    (let loop ([i 0])
      (when (< i n)
        (vector-set! ind i i) (loop (1+ i))))
    (let loop ([i n] [ll '()])
      (if (positive? i)
        (let ([j (random i)])
          (set! i (1- i))
          (unless (= i j)
            (let ([x (vector-ref ind i)] [y (vector-ref ind j)])
              (vector-set! ind i y) (vector-set! ind j x)))
          (loop i (cons (list-ref l (vector-ref ind i)) ll)))
        ll))))

(make-demo rbt avlt [bt 4] th [sl 1/2]))
;}}}

(random-seed (time-nanosecond (current-time)))
(import fset%)
