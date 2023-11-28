
    (check-assert (function? solve-sat))    ; correct name
    (check-error (solve-sat))                ; not 0 arguments
    (check-error (solve-sat 'x))             ; not 1 argument
    (check-error (solve-sat 'x (lambda () 'fail)))   ; not 2 args
    (check-error
       (solve-sat 'x (lambda () 'fail) (lambda (c r) 'succeed) 'z)) ; not 4 args

    (check-error (solve-sat 'x (lambda () 'fail) (lambda () 'succeed)))
        ; success continuation expects 2 arguments, not 0
    (check-error (solve-sat 'x (lambda () 'fail) (lambda (_) 'succeed)))
        ; success continuation expects 2 arguments, not 1
    (check-error (solve-sat
                       (make-and (list2 'x (make-not 'x)))
                       (lambda (_) 'fail)
                       (lambda (_) 'succeed)))
        ; failure continuation expects 0 arguments, not 1


    (check-expect   ; x can be solved
       (solve-sat 'x
                  (lambda () 'fail)
                  (lambda (cur resume) 'succeed))
       'succeed)

    (check-expect   ; x is solved by '((x #t))
       (solve-sat 'x
                  (lambda () 'fail)
                  (lambda (cur resume) (find 'x cur)))
       #t)

    (check-expect   ; (make-not 'x) can be solved
       (solve-sat (make-not 'x)
                  (lambda () 'fail)
                  (lambda (cur resume) 'succeed))
       'succeed)

    (check-expect   ; (make-not 'x) is solved by '((x #f))
       (solve-sat (make-not 'x)
                  (lambda () 'fail)
                  (lambda (cur resume) (find 'x cur)))
       #f)

    (check-expect   ; (make-and (list2 'x (make-not 'x))) cannot be solved
       (solve-sat (make-and (list2 'x (make-not 'x)))
                  (lambda () 'fail)
                  (lambda (cur resume) 'succeed))
       'fail)

