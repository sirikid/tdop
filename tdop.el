;; -*- lexical-binding: t; -*-

(defsubst tdop-make-var (env name &optional value)
  (declare (indent 2))
  (set (obarray-put env (symbol-name name)) value)
  env)

(defsubst tdop-var (env name)
  (when (symbolp name)
    (setq name (symbol-name name)))
  (or (obarray-get env name)
      (error "Variable `%s' is not defined" name)))

(defun tdop-env ()
  (let ((ob (obarray-make))
        (k 1))
    (tdop-make-var ob 'generate
      (lambda ()
        (prog1
            (vconcat
             (make-vector k 0)
             (make-vector k 1))
          (cl-incf k))))
    (tdop-make-var ob 'boole
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
    (tdop-make-var ob 'isvalid
      (lambda (x)
        (not (seq-some #'zerop x))))
    ob))

(defun tdop-eval (expr env)
  (pcase expr
    (`(,a <- ,b)
     (tdop-make-var env a (tdop-eval b env)))

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
     (apply (symbol-value (tdop-var env fun))
            (mapcar
             (lambda (expr)
               (tdop-eval expr env))
             args)))

    ((pred symbolp)
     (symbol-value (tdop-var env expr)))

    ((pred atom)
     expr)

    (_
     (error "Invalid expression: %s" expr))))


;; Major mode

(require 'smie)

(defun tdop-smie-forward-token ()
  (skip-syntax-forward "\\s-")
  (save-match-data
    (cond
     ((looking-at "[][()'!]")
      (goto-char (match-end 0))
      (match-string-no-properties 0))
     ((looking-at "\"")
      (goto-char (match-end 0))
      (parse-partial-sexp (point) (point-max) 0 nil nil 'syntax-table)
      (buffer-substring-no-properties (match-beginning 0) (point)))
     (t
      (smie-default-forward-token)))))

(defalias 'tdop-smie-backward-token #'smie-default-backward-token)

(defvar tdop-smie-grammar
  (smie-prec2->grammar
   (smie-bnf->prec2
    '((expr ("(" expr ")")
            (expr "<-" expr)
            (expr ";" expr)
            (expr "&" expr)
            ("if" expr "then" expr "else" expr)))
    '((left ";" "&")
      (right "<-")
      (nonassoc "else")))))

(defvar tdop-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\' "$" st)
    (modify-syntax-entry ?& "." st)
    (modify-syntax-entry ?* "." st)
    (modify-syntax-entry ?+ "." st)
    (modify-syntax-entry ?- "." st)
    (modify-syntax-entry ?↑ "." st)
    st))

(defvar tdop-font-lock-defaults '())

(define-derived-mode tdop-mode prog-mode "TDOP"
  (set-syntax-table tdop-syntax-table)
  (smie-setup tdop-smie-grammar #'ignore
              :forward-token #'tdop-smie-forward-token
              :backward-token #'tdop-smie-backward-token))

(defun tdop-tokenize ()
  (cl-loop for token = (tdop-smie-forward-token)
           until (string-empty-p token)
           collect token))


;; Tests...

(ert-deftest tdop-tokenize-assign ()
  (with-temp-buffer
    (tdop-mode)
    (insert "a ← b ← c ← d")
    (goto-char (point-min))
    (should (equal (tdop-tokenize) '("a" "←" "b" "←" "c" "←" "d")))))

(ert-deftest tdop-tokenize-quote ()
  (with-temp-buffer
    (tdop-mode)
    (insert "'1+1'")
    (goto-char (point-min))
    (should (equal (tdop-tokenize) '("'" "1" "+" "1" "'")))))

(ert-deftest tdop-tokenize-string ()
  (with-temp-buffer
    (tdop-mode)
    (insert "\"1+1\"")
    (goto-char (point-min))
    (should (equal (tdop-tokenize) '("\"1+1\"")))))

(ert-deftest tdop-tokenize-prog1 ()
  (with-temp-buffer
    (tdop-mode)
    (insert "a;b")
    (goto-char (point-min))
    (should (equal (tdop-tokenize) '("a" ";" "b")))))

(ert-deftest tdop-tokenize-prog2 ()
  (with-temp-buffer
    (tdop-mode)
    (insert "a&b")
    (goto-char (point-min))
    (should (equal (tdop-tokenize) '("a" "&" "b")))))

(ert-deftest tdop-tokenize-if ()
  (with-temp-buffer
    (tdop-mode)
    (insert "if q then w else e")
    (goto-char (point-min))
    (should (equal (tdop-tokenize) '("if" "q" "then" "w" "else" "e")))))

(ert-deftest tdop-tokenize-function-call ()
  (with-temp-buffer
    (tdop-mode)
    (insert "boole(1101, left, parse 1)")
    (goto-char (point-min))
    (should (equal (tdop-tokenize)
                   '("boole" "(" "1101" "," "left" "," "parse" "1" ")")))))

(ert-deftest tdop-tokenize-complex-expression ()
  (with-temp-buffer
    (tdop-mode)
    (insert "if 3*a + b!↑-3 = 0 then print a + (b-1) else rewind")
    (goto-char (point-min))
    (should (equal (tdop-tokenize)
                   '("if" "3" "*" "a" "+" "b" "!" "↑" "-3" "=" "0"
                     "then" "print" "a" "+" "(" "b" "-" "1" ")"
                     "else" "rewind")))))

(ert-deftest tdop-tokenize-prover ()
  (with-temp-buffer
    (tdop-mode)
    (insert-file-contents "prover.tdop")
    (goto-char (point-min))
    (should
     (equal
      (tdop-tokenize)
      '("nonud" "←" "'" "if" "null" "led" "(" "self" ")" "then" "nud" "(" "self" ")" "←" "generate" "else" "(" "print" "self" ";" "print" "\"has no argument\"" ")" "'" ";"
        "led" "(" "\"?\"" ")" "←" "'" "if" "left" "isvalid" "then" "print" "\"theorem\"" "else" "print" "\"non-theorem\"" ";" "parse" "1" "'" ";"
        "lbp" "(" "\"?\"" ")" "←" "1" ";"
        "nud" "(" "\"(\"" ")" "←" "'" "parse" "0" "&" "check" "\")\"" "'" "lbp" "(" "\")\"" ")" "←" "0" ";"
        "led" "(" "\"→\"" ")" "←" "'" "boole" "(" "[" "1" "1" "0" "1" "]" "," "left" "," "parse" "1" ")" "'" ";"
        "lbp" "(" "\"→\"" ")" "←" "2" ";"
        "led" "(" "\"∨\"" ")" "←" "'" "boole" "(" "[" "1" "1" "1" "0" "]" "," "left" "," "parse" "3" ")" "'" ";"
        "lbp" "(" "\"∨\"" ")" "←" "3" ";"
        "led" "(" "\"∧\"" ")" "←" "'" "boole" "(" "[" "1" "0" "0" "0" "]" "," "left" "," "parse" "4" ")" "'" ";"
        "lbp" "(" "\"∧\"" ")" "←" "4" ";"
        "nud" "(" "\"~\"" ")" "←" "'" "boole" "(" "[" "0" "1" "0" "1" "]" "," "parse" "5" "," "[" "0" "]" ")" "'")))))


;; ...

;; null-denotation, nud := t
;; left-denotation, led := number
;; left binding priority, lbp := number

(defun tdop-parse ()
  (tdop-run-semantic-code env token))

(defun tdop-run-semantic-code (env token)
  (let ((info (obarray-get env token)))
    (get info ')))

(defun tdop-parse-postfix ()
  )
