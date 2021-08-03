;;;; based on mikehw's solution, approx. 120x speedup
;;;
;;; run as:
;;;     sbcl --script PrimeSieve.lisp
;;;


;(load "bitvector-set-2.0.0.lisp")
;(load "bitvector-set-2.1.7.lisp")
;(load "bitvector-set-2.1.8-snap.lisp")


(declaim
  (optimize (speed 3) (safety 0) (debug 0) (space 0)))


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


(defclass sieve-state ()
  ((maxints :initarg :maxints
            :type fixnum
            :accessor sieve-state-maxints)

   (a       :initarg :a
            :type simple-bit-vector
            :accessor sieve-state-a)))


(defun create-sieve (maxints)
  (declare (fixnum maxints))
  (make-instance 'sieve-state
    :maxints maxints
    :a (make-array (ceiling maxints 2)
         :element-type 'bit
         :initial-element 0)))


(defun run-sieve (sieve-state)
  (declare (type sieve-state sieve-state))

  (let* ((rawbits (sieve-state-a sieve-state))
         (sieve-size (sieve-state-maxints sieve-state))
         (end (ceiling sieve-size 2))
         (q (floor (sqrt sieve-size)))
         (factor 3))
    (declare (fixnum sieve-size end q factor) (type simple-bit-vector rawbits))
    (loop while (<= factor q) do

      (loop for num fixnum
            from factor
            to q
            by 2
            until (zerop (sbit rawbits (floor num 2)))
            finally (setq factor num))

      (let* ((i0 (floor (the fixnum (* factor factor)) 2))
             (i1 (+ i0 factor))
             (i2 (+ i1 factor))
             (i3 (+ i2 factor))
             (factor4 (* 4 factor)))
        (declare (fixnum i0 i1 i2 i3 factor4))

        (loop while (< i3 end)
              do (setf (sbit rawbits i0) 1)  (incf i0 factor4)
                 (setf (sbit rawbits i1) 1)  (incf i1 factor4)
                 (setf (sbit rawbits i2) 1)  (incf i2 factor4)
                 (setf (sbit rawbits i3) 1)  (incf i3 factor4))
    
        (loop while (< i0 end)
              do (setf (sbit rawbits i0) 1)
                 (incf i0 factor)))

      (incf factor 2))
    sieve-state))


(defun count-primes (sieve-state)
  (reduce #'+ (sieve-state-a sieve-state) :key (lambda (n) (- 1 n))))


(defun list-primes (result)
  (princ "2, " *error-output*)
  (let ((bits (sieve-state-a result)))
    (loop for i
          from 3
          to (min *list-to* (sieve-state-maxints result))
          by 2 do
      (when (zerop (sbit bits (floor i 2)))
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



;(require :sb-sprof) (sb-sprof:with-profiling (:max-samples 1000 :report :flat :loop nil)

(let* ((passes 0)
       (start (get-internal-real-time))
       (end (+ start (* internal-time-units-per-second 5)))
       result)
  (declare (fixnum passes))

  (do () ((>= (get-internal-real-time) end))
    (setq result (run-sieve (create-sieve 1000000)))
    (incf passes))

  (let* ((duration  (/ (- (get-internal-real-time) start) internal-time-units-per-second))
         (avg (/ duration passes)))
    (when *list-to* (list-primes result))
    (format *error-output* "Algorithm: base  Passes: ~d  Time: ~f  Avg: ~f ms  Count: ~d  Valid: ~A~%"
            passes duration (* 1000 avg) (count-primes result) (validate result))

    (format t "mayerrobert-cl;~d;~f;1;algorithm=base,faithful=yes,bits=1~%" passes duration)))

;) (disassemble 'run-sieve)


#+nil
; Same timed loop again, this time there is "#." before the invocation of run-sieve.
; See http://clhs.lisp.se/Body/02_dh.htm for what #. does.
(let* ((passes 0)
       (start (get-internal-real-time))
       (end (+ start (* internal-time-units-per-second 5)))
       result)
  (declare (fixnum passes))

  (do () ((>= (get-internal-real-time) end))
    (setq result #. (run-sieve (create-sieve 1000000)))
    (incf passes))

  (let* ((duration  (/ (- (get-internal-real-time) start) internal-time-units-per-second))
         (avg (/ duration passes)))
    (when *list-to* (list-primes result))
    (format *error-output* "Algorithm: base  Passes: ~d  Time: ~f  Avg: ~f ms  Count: ~d  Valid: ~A~%"
            passes duration (* 1000 avg) (count-primes result) (validate result))

    (format t "mayerrobert-cl-hashdot;~d;~f;1;algorithm=base,faithful=no,bits=1~%" passes duration)))
