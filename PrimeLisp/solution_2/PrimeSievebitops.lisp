;;;; loosely based on sieve_1of2.c by  by Daniel Spangberg
;;;
;;; set-bits-dense based on https://github.com/PlummersSoftwareLLC/Primes/pull/680
;;;
;;; run as:
;;;     sbcl --script PrimeSievebitops.lisp
;;;


(declaim
  (optimize (speed 3) (safety 0) (debug 0) (space 0))

  (inline or-bit)
  (inline nth-bit-set-p)
  (inline set-nth-bit)

  (inline set-bits-simple)
  (inline set-bits-unrolled)
  (inline set-bits-dense))


(defparameter *list-to* 100
  "list primes up to that number, set to nil to disable listing")


(defconstant +results+
  '((         10 . 4        )
    (        100 . 25       )
    (        127 . 31       )
    (        128 . 31       )
    (        129 . 31       )
    (       1000 . 168      )
    (      10000 . 1229     )
    (     100000 . 9592     )
    (    1000000 . 78498    )
    ;(   10000000 . 664579   )  ; probably some ubyte64 overflow
    )
  "Historical data for validating our results - the number of primes
   to be found under some limit, such as 168 primes under 1000")


#+64-bit (defconstant +bits-per-word+ 64)
#-64-bit (defconstant +bits-per-word+ 32)

(deftype nonneg-fixnum ()
  `(integer 0 ,most-positive-fixnum))
  ;`(unsigned-byte ,+bits-per-word+))

(deftype sieve-element-type ()
  `(unsigned-byte ,+bits-per-word+))

(deftype sieve-array-type ()
  `(simple-array sieve-element-type 1))


(defclass sieve-state ()
  ((maxints :initarg :maxints
            :type nonneg-fixnum
            :accessor sieve-state-maxints)

   (a       :initarg :a
            :type sieve-array-type
            :accessor sieve-state-a)))


(defun create-sieve (maxints)
  (declare (nonneg-fixnum maxints))
  (make-instance 'sieve-state
    :maxints maxints
    :a (make-array (ceiling (ceiling maxints +bits-per-word+) 2)
         :element-type 'sieve-element-type
         :initial-element 0)))


(defun nth-bit-set-p (a n)
  "Returns t if n-th bit is set in array a, nil otherwise."
  (declare (sieve-array-type a)
           (nonneg-fixnum n))
  (multiple-value-bind (q r) (floor n +bits-per-word+)
    (declare (nonneg-fixnum q r))
    (logbitp r (aref a q))))


(defun or-bit (a idx bit)
  "Set bit in array a at the given word-index and bit-position to 1."
  (let ((pattern (ash 1 bit)))
    (declare (type sieve-element-type pattern))
    (setf #1=(aref a idx) (logior #1# pattern))))


(defun set-nth-bit (a n)
  "Set n-th bit in array a to 1."
  (declare (type sieve-array-type a)
           (type nonneg-fixnum n))
  (multiple-value-bind (q r) (floor n +bits-per-word+)
    (declare (nonneg-fixnum q r))
    (or-bit a q r)))


(defun set-bits-simple (bits first-incl last-excl every-nth)
  "Set every every-nth bit in array bits between first-incl and last-excl."
  (declare (type nonneg-fixnum first-incl last-excl every-nth)
           (type sieve-array-type bits))
  (loop while (< first-incl last-excl)
        do (set-nth-bit bits first-incl)
           (incf first-incl every-nth)))


(defun set-bits-unrolled (bits first-incl last-excl every-nth)
  "Set every every-nth bit in array bits between first-incl and last-excl."
  (declare (type nonneg-fixnum first-incl last-excl every-nth)
           (type sieve-array-type bits))

  ; use an unrolled loop to set every every-th bit to 1
  (let* ((i first-incl)
         (every-nth-times-2 (+ every-nth every-nth))
         (every-nth-times-3 (+ every-nth-times-2 every-nth))
         (every-nth-times-4 (+ every-nth-times-3 every-nth)))
    (declare (nonneg-fixnum i every-nth-times-2 every-nth-times-3 every-nth-times-4))

    (when (> last-excl (the nonneg-fixnum (+ i every-nth-times-4)))
      (loop with end1 of-type nonneg-fixnum = (- last-excl every-nth-times-4)
            while (< i end1)
            do (set-nth-bit bits i)
               (set-nth-bit bits (+ i every-nth))
               (set-nth-bit bits (+ i every-nth-times-2))
               (set-nth-bit bits (+ i every-nth-times-3))
               (incf i every-nth-times-4)))

    (set-bits-simple bits i last-excl every-nth)))


(defun generate-set-bits-modulo (startbit n)
  "Generate statements to set every nth bit in n words, starting at startbit.
The generated code contains references to the variable 'startword'."
  (loop for word
        from 0
        below n
        append (if (> (+ startbit n) +bits-per-word+)

                     (prog1 `((setf (aref bits (+ startword ,(+ word (floor startbit +bits-per-word+))))
                           (logior (aref bits (+ startword ,(+ word (floor startbit +bits-per-word+))))
                                   ,(ash 1 (mod startbit +bits-per-word+)))))
                       (incf startbit n)
                       (decf startbit +bits-per-word+))

                 (append `((setq tmp (logior (aref bits (+ startword ,(+ word (floor startbit +bits-per-word+))))
                                             ,(ash 1 (mod startbit +bits-per-word+)))))
                         (loop for i from (+ startbit n) below (- +bits-per-word+ n) by n
                               collect `(setq tmp (logior tmp ,(ash 1 i))) into ret
                               finally (return (prog1 (append ret
                                                              `((setf (aref bits (+ startword ,(+ word (floor startbit +bits-per-word+))))
                                                                      (logior tmp
                                                                              ,(ash 1 (mod i +bits-per-word+))))))
                                                      (setq startbit i)
                                                      (incf startbit n)
                                                      (decf startbit +bits-per-word+))))))))


(defun generate-dense-loop (first n)
  "Generate a loop statement to set every nth bit, starting at first.
The generated code contains references to the variable ''last-excl'."
  `((let ((startword 0) (tmp 0))
      (declare (type sieve-element-type tmp))
      ,@(generate-set-bits-modulo first n))

    (loop with tmp of-type sieve-element-type
          for bit of-type nonneg-fixnum
          from ,(* n +bits-per-word+)
          below (- last-excl ,(* n +bits-per-word+))
          by ,(* n +bits-per-word+)
          do (let ((startword (floor bit +bits-per-word+)))
               ,@(generate-set-bits-modulo (mod (+ first (* n +bits-per-word+)) n) n))
          finally (set-bits-unrolled bits (+ bit ,(mod (+ first (* n +bits-per-word+)) n)) last-excl ,n))))


(defmacro generate-cond-stmt ()
  "Expand into a cond stmt whose branches all set every 'every-nth' bit in the array 'bits'.
The generated code contains references to the variables 'bits', 'first-incl', 'last-excl' and 'every-nth'.
Branches for low values of 'every-nth' (up to 31) will set bits using unrolled dense loops, fallback for higher values is calling 'set-bits-unrolled'."
  `(if (< every-nth (floor last-excl +bits-per-word+))
         (cond ,@(loop for x from 3 to 31 by 2
                       collect `((= every-nth ,x)
                                 ,@(generate-dense-loop (floor (expt x 2) 2) x)) into cases
                       finally (return (append cases
                                              `((t (set-bits-unrolled bits first-incl last-excl every-nth)))))))
     (set-bits-unrolled bits first-incl last-excl every-nth)))


; uncomment the following line to display the generated cond stmt containing dense bit-setting loops for the first few distances
;(format *error-output* "Expansion of macro generate-cond-stmt:~%~A~%" (macroexpand-1 '(generate-cond-stmt)))


(defun set-bits-dense (bits first-incl last-excl every-nth)
  "Set every every-nth bit in array bits between first-incl and last-excl."
  (declare (type nonneg-fixnum first-incl last-excl every-nth)
           (type sieve-array-type bits))
  (generate-cond-stmt))


(defun run-sieve (sieve-state)
  (declare (type sieve-state sieve-state))

  (let* ((rawbits (sieve-state-a sieve-state))
         (sieve-size (sieve-state-maxints sieve-state))
         (sieve-sizeh (ceiling sieve-size 2))
         (factor 0)
         (factorh 1)
         (qh (ceiling (floor (sqrt sieve-size)) 2)))
    (declare (nonneg-fixnum sieve-size sieve-sizeh factor factorh qh) (type sieve-array-type rawbits))
    (loop do

      (loop for num of-type nonneg-fixnum
            from factorh
            to qh
            while (nth-bit-set-p rawbits num)
            finally (setq factor (1+ (* num 2)))
                    (setq factorh (1+ num)))

      (when (> factorh qh)
        (return-from run-sieve sieve-state))

      (set-bits-dense rawbits (floor (the nonneg-fixnum (* factor factor)) 2) sieve-sizeh factor))
    sieve-state))


(defun count-primes (sieve-state)
  (declare (sieve-state sieve-state))
  (let ((max (sieve-state-maxints sieve-state))
        (bits (sieve-state-a sieve-state))
        (result 0))
    (declare (nonneg-fixnum result))
    (loop for i of-type nonneg-fixnum
          from 1
          to max
          by 2
          do
      (unless (nth-bit-set-p bits (floor i 2))
        (incf result)))
    result))


(defun list-primes (result)
  (princ "2, " *error-output*)
  (let ((bits (sieve-state-a result)))
    (loop for i
          from 3
          to (min *list-to* (sieve-state-maxints result))
          by 2 do
      (unless  (nth-bit-set-p bits (floor i 2))
        (format *error-output* "~d, " i))))
  (when (< *list-to* (sieve-state-maxints result))
    (princ "..." *error-output*))
  (terpri *error-output*))


(defun test ()
  "Run run-sieve on all historical data in +results+, return nil if there is any deviation."
  (let ((result t))
    (mapc #'(lambda (tupel)
              (unless (= (cdr tupel) (count-primes (run-sieve (create-sieve (car tupel)))))
                (format *error-output* "ERROR: ~d produces wrong result~%" (car tupel))
                (setq result nil)))
            +results+)
    result))


(defun validate (sieve-state)
  "Invoke test, and then check if sieve-state is correct
according to the historical data in +results+."
  (let ((hist (cdr (assoc (sieve-state-maxints sieve-state) +results+ :test #'=))))
    (if (and (test) hist (= (count-primes sieve-state) hist)) "yes" "no")))


(let* ((passes 0)
       (start (get-internal-real-time))
       (end (+ start (* internal-time-units-per-second 5)))
       result)
  (declare (nonneg-fixnum passes))

  (loop while (<= (get-internal-real-time) end)
        do (setq result (run-sieve (create-sieve 1000000)))
           (incf passes))

  (let* ((duration  (/ (- (get-internal-real-time) start) internal-time-units-per-second))
         (avg (/ duration passes)))
    (when *list-to* (list-primes result))
    (format *error-output* "Algorithm: base w/ dense bitops  Passes: ~d  Time: ~f Avg: ~f ms Count: ~d  Valid: ~A~%"
            passes duration (* 1000 avg) (count-primes result) (validate result))

    (format t "mayerrobert-cl-dense;~d;~f;1;algorithm=base,faithful=yes,bits=1~%" passes duration)))
