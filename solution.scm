;;;;;;;;;;;;;;;;;;;;;;;; COMP 105 CONTINUATIONS ASSIGNMENT ;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Problem 2
;;

;; (list-of? A? v) returns #t if all the values in a list v satisfy the function
;; A?

;; laws:
;; (list-of? A? '()) == #t
;; (list-of? A? (cons v vs)) == (&& (A? v) (list-of? A? vs))
;; (list-of? A? v) == #f , where v is not '() and v is not (cons v vs)

(define list-of? (A? v)
    (if (null? v)
        #t
        (if (pair? v)
            (&& (A? (car v)) (list-of? A? (cdr v)))
            #f)))

        (check-assert(list-of? pair? '()))
        (check-assert (list-of? function? '()))
        (check-assert (not(list-of? function? '(+ - * / function?))))
        (check-assert (list-of? number? '(-2 -1 0 1 2 100)))
        (check-assert (not(list-of? number? '(0 1 2 + number?))))
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Problem 3
;;

;; Records
(record not [arg])
(record or [args])
(record and [args])

;; (formula? s) returns #t if a value s represents a symbol, or applies the
;; various rules for make-or and make-and respectively if s is a list
;; of formulas, or the rules for make-not accordingly if s is a Boolean formula
;; itself

;; laws:
;; (formula? s) == #t, where s is a symbol
;; (formula? (make-not f)) == (formula? s), where f is a formula
;; (formula? (make-or fs)) == (list-of? formula? fs),
;;                            where fs is a list of formulas
;; (formula? (make-and fs)) == (list-of? formula? fs),
;;                            where fs is a list of formulas

(define formula? (s)
    (if (symbol? s)
        #t
        (if (not? s)
            (formula? (not-arg s))
            (if (or? s)
                (list-of? formula? (or-args s))
                (if (and? s)
                    (list-of? formula? (and-args s))
                    #f)))))

        
        (check-error  (formula? x))
        (check-assert (formula? 'x))
        (check-assert (not (formula? '(x))))
        (check-assert (formula? (make-or '())))
        (check-assert (formula? (make-and '())))
        (check-assert (not (formula? (make-not '()))))
        (check-assert (formula? (make-or '(a b c d e f g h i))))
        (check-assert (formula? (make-or (list2 'a (make-not 'b)))))
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Problem 4
;;

;; (eval-formula f env) returns True when the function f is satisfied in the
;; environment env

;; laws
;; (eval-formula f env) == (find f env), where f is a symbol
;; (eval-formula (make-not f) env) == (not (eval-formula (not-arg f) env))
;; (eval-formula (make-or fs) env) ==
;;      (foldl (lambda (x accum) (|| (eval-formula x env))) #t (or-args fs))
;; (eval-formula (make-and fs) env) ==
;;      (foldl (lambda (x accum) (&& (eval-formula x env))) #t (and-args fs))

(define eval-formula (f env)
    (if (symbol? f)
        (find f env)
        (if (not? f)
            (not (eval-formula (not-arg f) env))
            (if (or? f)
                (foldl (lambda (x accum)
                            (|| (eval-formula x env))) #f (or-args f))
                (foldl (lambda (x accum)
                            (&& (eval-formula x env))) #t (and-args f))))))

        (check-assert (function? eval-formula))
        (check-error (eval-formula 'y))
        (check-assert (eval-formula 'y '((y #t))))
        (check-assert (eval-formula 'a '((a #t) (b #f))))
        (check-assert (not (eval-formula 'b '((a #t) (b #f)))))
        (check-assert (eval-formula (make-or (list2 'a (make-not 'b))) 
                                                '((a #t)(b #f))))
        (check-assert (eval-formula (make-or (list2 'a 'b)) 
                                                '((a #f)(b #t))))
        (check-assert (eval-formula (make-and (list2 'a (make-not 'b))) 
                                                '((a #t)(b #f))))
        (check-assert (eval-formula (make-and (list2 'a 'b)) 
                                                '((a #t)(b #t))))
        (check-assert (not (eval-formula (make-and (list2 'a 'b)) 
                                                '((a #t)(b #f)))))
        (check-assert (not (eval-formula (make-and (list2 'a 'b)) 
                                                '((a #f)(b #f)))))
        (check-assert (not (eval-formula (make-or (list2 'a 'b)) 
                                                '((a #f)(b #f)))))
        (check-assert (not (eval-formula (make-or (list2 'a 'b)) 
                                                '((a #f)(b #f)))))
        (check-assert (eval-formula (make-not 'b) '((a #t)(b #f))))
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Problem 5
;;

;; (solve-sat f succ fail) returns succ if there is an assignment for formula f
;; that is satisfied, otherwise, it returns fail

(define solve-sat (f fail succ)
    (letrec ([solve-formula

                ;; extends cur to find an assignment that makes a formula equal
                ;; to bool.

                ;;laws:
                ;; (solve-formula x bool cur fail succ) ==
                ;;          (solve-symbol x bool cur fail succ), x is a symbol
                ;; (solve-formula (make-not f) bool cur fail succ) == 
                ;;          (solve-formula f (not bool) cur fail succ)
                ;; (solve-formula (make-and fs)   #t cur fail succ) ==
                ;;          (solve-all fs #t cur fail succ)
                ;; (solve-formula (make-and fs)   #f cur fail succ) == 
                ;;          (solve-all fs #f cur fail succ)
                ;; (solve-formula (make-or fs)  #t cur fail succ) == 
                ;;          (solve-any fs #t cur fail succ)
                ;; (solve-formula (make-or fs)  #f cur fail succ) == 
                ;;          (solve-any fs #f cur fail succ)

                (lambda (f bool cur fail succ)
                    (if (symbol? f)
                        (solve-symbol f bool cur fail succ)
                        (if (not? f)
                            (solve-formula (not-arg f) (not bool) cur fail succ)
                            (if (and? f)
                                (solve-all (and-args f) bool cur fail succ)
                                (if (or? f)
                                    (solve-any (or-args f) bool cur fail succ)
                                    (fail))))))]
            
            
                [solve-all

                    ;; solve-all extends cur to find an assignment that makes
                    ;; all formulas in the list fs equal to bool.

                    ;;laws:
                    ;; (solve-all '() bool cur fail succ) == (succ cur fail)
                    ;; (solve-all (cons f fs) bool cur fail succ) == 
                    ;;      (solve-formula f bool cur fail 
                    ;;          (lambda (cur resume)
                    ;;              (solve-all fs bool cur resume succ)))
                    
                    (lambda (fs bool cur fail succ)
                        (if (null? fs)
                            (succ cur fail)
                            (solve-formula (car fs) bool cur fail
                                (lambda (cur resume)
                                    (solve-all (cdr fs) bool cur resume
                                        succ)))))]
                

                [solve-any

                    ;; solve-any extends cur to find an assignment that makes
                    ;; any one of the formulas in the list fs equal to bool.

                    ;; laws:
                    ;; (solve-any '()         bool cur fail succ) == (fail)
                    ;; (solve-any (cons f fs) bool cur fail succ) == 
                    ;;      (solve-formula f bool cur 
                    ;;          (lambda () (solve-any fs bool cur fail succ))
                    ;;              succ)

                    (lambda (fs bool cur fail succ)
                        (if (null? fs)
                            (fail)
                            (solve-formula (car fs) bool cur
                                (lambda () (solve-any (cdr fs) bool cur fail
                                            succ))
                                succ)))]
                
                [solve-symbol

                    ;; solve-symbol succs if the binding of x in cur satisfies
                    ;; bool or fails if not otherwise it creates a new binding

                    ;; laws:
                    ;; (solve-symbol x bool cur fail succ) == 
                    ;;    (succ (bind x bool cur) fail), where x is not bound in
                    ;;      cur
                    ;; (solve-symbol x bool cur fail succ) == (succ cur fail),
                    ;;      where x is bool in cur
                    ;; (solve-symbol x bool cur fail succ) == (fail), 
                    ;;      where x is not bool in cur

                    (lambda (x bool cur fail succ)
                        (if (= (find x cur) (not bool))
                            (fail)
                            (if (= (find x cur)  bool)
                                (succ cur fail)
                                (succ (bind x bool cur) fail))))])
                
                (solve-formula f #t '() fail succ)))


        (check-assert (function? solve-sat))
        (check-assert (solve-sat 'y (lambda () 'fail)
                        (lambda (cur resume) (find 'y cur))))

        (check-error  (solve-sat))
        (check-error  (solve-sat 'y))
        (check-error  (solve-sat 'y (lambda () 'fail)))
        (check-error  (solve-sat 'y (lambda () 'fail) (lambda (a b) 'succ) 'c))
        (check-error  (solve-sat 'y (lambda () 'fail) (lambda () 'succ)))
        (check-error  (solve-sat 'y (lambda () 'fail) (lambda (_) 'succ)))
        (check-error  (solve-sat (make-and (list2 'y (make-not 'y)))
                              (lambda (_) 'fail) (lambda (_) 'succ)))
    
        (check-expect (solve-sat 'y (lambda () 'fail)
                        (lambda (cur resume) 'succ)) 'succ)
        (check-expect (solve-sat (make-and (list2 'y (make-not 'y)))
                        (lambda () 'fail) (lambda (cur resume) 'succ)) 'fail)
        (check-expect (solve-sat (make-or (list2 'y (make-not 'y)))
                        (lambda () 'fail) (lambda (cur resume) 'succ)) 'succ)
        (check-expect (solve-sat (make-not 'y) (lambda () 'fail)
                        (lambda (cur resume) 'succ))'succ)
        (check-expect (solve-sat (make-not 'y) (lambda () 'fail)
                        (lambda (cur resume) (find 'y cur))) #f)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;