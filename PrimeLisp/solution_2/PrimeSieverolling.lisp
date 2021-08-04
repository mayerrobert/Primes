;;;; based on sieve_1of2.c by  by Daniel Spangberg
;;;
;;; run as:
;;;     sbcl --script PrimeSieverolling.lisp
;;;


(declaim
  (optimize (speed 3) (safety 0) (debug 0) (space 0))

  (inline nth-bit-set-p)
  (inline set-nth-bit)
  (inline rotl)
  (inline set-bits))


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
    (   10000000 . 664579   ))
  "Historical data for validating our results - the number of primes
   to be found under some limit, such as 168 primes under 1000")


#+64-bit (defconstant +bits-per-word+ 64)
#-64-bit (defconstant +bits-per-word+ 32)

(deftype nonneg-fixnum ()
  `(integer 0 ,most-positive-fixnum))

(deftype sieve-element-type ()
  `(unsigned-byte ,+bits-per-word+))

(deftype sieve-array-type ()
  `(simple-array sieve-element-type 1))


(defclass sieve-state ()
  ((maxints :initarg :maxints
            :type fixnum
            :accessor sieve-state-maxints)

   (a       :initarg :a
            :type sieve-array-type
            :accessor sieve-state-a)))


(defun create-sieve (maxints)
  (declare (fixnum maxints))
  (make-instance 'sieve-state
    :maxints maxints
    :a (make-array (1+ (floor (floor maxints +bits-per-word+) 2))
         :element-type 'sieve-element-type
         :initial-element 0)))


(defun nth-bit-set-p (a n)
  "Returns t if n-th bit is set in array a, nil otherwise."
  (declare (sieve-array-type a)
           (fixnum n))
  (multiple-value-bind (q r) (floor n +bits-per-word+)
    (declare (fixnum q r))
    (logbitp r (aref a q))))

(defun set-nth-bit (a n)
  "Set n-th bit in array a to 1."
  (declare (type sieve-array-type a)
           (type fixnum n))
  (multiple-value-bind (q r) (floor n +bits-per-word+)
    (declare (fixnum q r))
    (setf #1=(aref a q)
         (logior #1# (expt 2 r)))) 0)


(defmacro mrotl (x bits)
  "Compute bitwise left rotation of x by 'bits' bits, represented on 'width' bits"
  ;(declare (type sieve-element-type x) (type nonneg-fixnum bits))
  `(logior (logand (ash ,x ,bits)
                   ,(1- (ash 1 +bits-per-word+)))
           (logand (ash ,x (- (- +bits-per-word+ ,bits)))
                   ,(1- (ash 1 +bits-per-word+)))))

(defun rotl (x bits)
  "Compute bitwise left rotation of x by 'bits' bits, represented on 'width' bits"
  (declare (type sieve-element-type x) (type (integer 0 #.(1- +bits-per-word+)) bits))
  (logior (logand (ash x bits)
                   #.(1- (ash 1 +bits-per-word+)))
           (logand (ash x (- (- +bits-per-word+ bits)))
                   #.(1- (ash 1 +bits-per-word+)))))


; from solution_1/PrimeCPP.cpp
;
; void setFlagsFalse(size_t n, size_t skip) {
;     auto rolling_mask = ~uint32_t(1 << n % 32);
;     auto roll_bits = skip % 32;
;     while (n < arrSize) {
;         array[index(n)] &= rolling_mask;
;         n += skip;
;         rolling_mask = rol(rolling_mask, roll_bits);
;     }
; }


(defun set-bits (bits n size skip)
  "Set every every-nth bit in array bits between first-incl and last-excl."
  (declare (type nonneg-fixnum n size skip)
           (type sieve-array-type bits))
  (let ((rolling-mask (expt 2 (mod n +bits-per-word+)))
        (roll-bits (mod skip +bits-per-word+)))
    (declare (type nonneg-fixnum roll-bits)
             (type sieve-element-type rolling-mask))
    (loop while (< n size) do
      (setf #1=(aref bits (floor n +bits-per-word+))
            (logior #1# rolling-mask))
      (incf n skip)
      (setq rolling-mask (rotl rolling-mask roll-bits)))))


#+nil
(defun set-bits (bits first-incl last-excl every-nth)
  "Set every every-nth bit in array bits between first-incl and last-excl."
  (declare (type fixnum first-incl last-excl every-nth)
           (type sieve-array-type bits))
  (loop for num of-type fixnum
        from first-incl
        to (1- last-excl)
        by every-nth
        do (set-nth-bit bits num)))


(defun run-sieve (sieve-state)
  (declare (type sieve-state sieve-state))

  (let* ((rawbits (sieve-state-a sieve-state))
         (sieve-size (sieve-state-maxints sieve-state))
         (sieve-sizeh (ceiling sieve-size 2))
         (factor 0)
         (factorh 1)
         (qh (ceiling (floor (sqrt sieve-size)) 2)))
    (declare (nonneg-fixnum sieve-size sieve-sizeh factor factorh qh) (type sieve-array-type rawbits))
    (loop while (<= factorh qh) do

      (loop for num of-type nonneg-fixnum
            from factorh
            to qh
            while (nth-bit-set-p rawbits num)
            finally (setq factor (1+ (* num 2)))
                    (setq factorh (1+ num)))

      (set-bits rawbits (floor (the nonneg-fixnum (* factor factor)) 2) sieve-sizeh factor))
    sieve-state))


(defun count-primes (sieve-state)
  (declare (sieve-state sieve-state))
  (let ((max (sieve-state-maxints sieve-state))
        (bits (sieve-state-a sieve-state))
        (result 0))
    (declare (fixnum result))
    (loop for i fixnum
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
  (declare (fixnum passes))

  (do () ((>= (get-internal-real-time) end))
    (setq result (create-sieve 1000000))
    (run-sieve result)
    (incf passes))

  (let* ((duration  (/ (- (get-internal-real-time) start) internal-time-units-per-second))
         (avg (/ duration passes)))
    (when *list-to* (list-primes result))
    (format *error-output* "Algorithm: base w/ rolling bitops  Passes: ~d  Time: ~f Avg: ~f ms Count: ~d  Valid: ~A~%"
            passes duration (* 1000 avg) (count-primes result) (validate result))

    (format t "mayerrobert-cl-rolling;~d;~f;1;algorithm=base,faithful=yes,bits=1~%" passes duration)))

(print (macroexpand-1 '(rotl x n)))

(defparameter +a+ (make-array 1 :element-type 'sieve-element-type :initial-element 0))
(disassemble '(lambda (x n)
                (declare (type (unsigned-byte #.+bits-per-word+) x)
                         (type (integer 0 #.(1- +bits-per-word+)) n))
                (declare (type (simple-array sieve-element-type 1) +a+))
                (setf (aref +a+ 0) (rotl x n))
                nil))
