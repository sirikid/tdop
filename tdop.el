;; -*- lexical-binding: t; -*-

(defmacro tdop-var (env name)
  `(symbol-value (obarray-put ,env (symbol-name ,name))))

(defun tdop-env ()
  (let ((ob (obarray-make))
        (k 1))
    (setf (tdop-var ob 'generate)
          (lambda ()
            (prog1
                (vconcat
                 (make-vector k 0)
                 (make-vector k 1))
              (cl-incf k))))
    (setf (tdop-var ob '&and) [1 0 0 0]
          (tdop-var ob '&or)  [1 1 1 0]
          (tdop-var ob '&eqv) [1 0 0 1])
    (setf (tdop-var ob 'boole)
          (lambda (m x y)
            (let (result (i 0) (j 0))
              (while (and (< i (length x))
                          (< j (length y)))
                (push (aref m (- 3 (* 2 (aref x i)) (aref y j)))
                      result)
                (cl-incf i)
                (cl-incf j)
                (pcase (cons (= i (length x))
                             (= j (length y)))
                  ('(t . nil) (setq i 0))
                  ('(nil . t) (setq j 0))))
              (vconcat (nreverse result)))))
    (setf (tdop-var ob 'isvalid)
          (lambda (x)
            (not (seq-some #'zerop x))))
    ob))

(defun tdop-eval (expr env)
  (pcase expr
    (`(,a <- ,b)
     (setf (tdop-var env a) (tdop-eval b env)))

    (`(\' ,a \') a)

    ;; covered by (pred atom)
    ;; ((pred stringp) expr)

    (`(,a \; ,b)
     (progn
       (tdop-eval a env)
       (tdop-eval b env)))

    (`(,a \& ,b)
     (prog1
         (tdop-eval a env)
       (tdop-eval b env)))

    (`(,(and (pred symbolp) fun)
       ,(and (pred listp) args))
     (apply (tdop-var env fun)
            (mapcar
             (lambda (expr)
               (tdop-eval expr env))
             args)))

    ((pred symbolp)
     (tdop-var env expr))

    ((pred atom)
     expr)

    (_
     (error "Invalid expression: %s" expr))))

;; a <- 10; boole(1001, generate(), generate())
(tdop-eval '((a <- 10) \; (boole(&eqv (generate()) (generate ())))) (tdop-env))

;; a <- 1001; b <- generate(); c <- generate(); boole(a, c, b)
(tdop-eval '((a <- &and) \;
             ((b <- (generate())) \;
              ((c <- (generate())) \;
               (boole(a c b)))))
           (tdop-env))
