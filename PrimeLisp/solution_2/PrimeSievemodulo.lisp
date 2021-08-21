;;;; based on https://github.com/PlummersSoftwareLLC/Primes/pull/641
;;;
;;; run as:
;;;     sbcl --script PrimeSievemodulo.lisp
;;;


;(declaim
;  (optimize (speed 3) (safety 0) (debug 0) (space 0))
;
;  (inline nth-bit-set-p)
;  (inline set-nth-bit)
;  (inline set-bits))


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
;    (   10000000 . 664579   )
    )
  "Historical data for validating our results - the number of primes
   to be found under some limit, such as 168 primes under 1000")


#+64-bit (defconstant +bits-per-word+ 8)
#-64-bit (defconstant +bits-per-word+ 32)

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
    :a (make-array (ceiling (ceiling maxints +bits-per-word+) 2)
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


(defmacro or-word (a idx pattern)
  `(progn
     (when *debug* (format t "word ~d, pattern ~8,'0b ~d~%" ,idx ,pattern ,pattern))
     (setf (aref ,a ,idx) (logior (aref ,a ,idx) ,pattern))))


(defparameter *debug* nil)

(defun set-bits (bits first-incl last-excl every-nth)
  "Set every every-nth bit in array bits between first-incl and last-excl."
  (declare (type fixnum first-incl last-excl every-nth)
           (type sieve-array-type bits))

;  (let ((l +bits-per-word+))
;    (format t "every = ~4d, every % l = ~2d, first = ~6d, first % l = ~2d, n-ops = ~d~%"
;            every-nth (mod every-nth l) first-incl (mod first-incl l) (floor (- 500000 first-incl) every-nth)))

  (let ((startmod (mod first-incl +bits-per-word+))
        (skipmod (mod every-nth +bits-per-word+)))
  (case skipmod
    (3
     (let* ((i first-incl)
            (span (* +bits-per-word+ every-nth))

            (bulkstartword (floor first-incl +bits-per-word+))
            (bulkstart     (* bulkstartword +bits-per-word+))

            (bulkendword   (floor (- last-excl span) +bits-per-word+))
            (bulkend       (* bulkendword +bits-per-word+))
            )
       (declare (fixnum i span bulkstartword bulkstart bulkendword bulkend))

       (when *debug*
         (format t "first-incl ~d, last-excl ~d, every ~d~%" first-incl last-excl every-nth)
         (format t "bulkstart  ~d, bulkend   ~d, end   ~d~%" bulkstart bulkend last-excl)
         (format t "bulkstartw ~d, bulkendw  ~d, end   ~d~%" bulkstartword bulkendword last-excl)
         (format t "span ~d, startmod   ~d~%" span startmod))

       (when (< bulkstart last-excl)

;       (loop while (< i bulkend)
;             do ;(set-nth-bit bits i)
;                (or-word bits
;                         (ash i #.(- (logcount (1- +bits-per-word+))))
;                         (ash 1 (logand i #.(1- +bits-per-word+))))
;                (incf i every-nth))

       (loop for word fixnum
             from bulkstartword
             to (1- bulkendword)
             by every-nth
             do (or-word bits (+ word (floor (+ startmod (* 0 every-nth)) +bits-per-word+)) (ash 1 (mod (+ startmod (* 0 every-nth)) +bits-per-word+)))
                (or-word bits (+ word (floor (+ startmod (* 1 every-nth)) +bits-per-word+)) (ash 1 (mod (+ startmod (* 1 every-nth)) +bits-per-word+)))
                (or-word bits (+ word (floor (+ startmod (* 2 every-nth)) +bits-per-word+)) (ash 1 (mod (+ startmod (* 2 every-nth)) +bits-per-word+)))
                (or-word bits (+ word (floor (+ startmod (* 3 every-nth)) +bits-per-word+)) (ash 1 (mod (+ startmod (* 3 every-nth)) +bits-per-word+)))
                (or-word bits (+ word (floor (+ startmod (* 4 every-nth)) +bits-per-word+)) (ash 1 (mod (+ startmod (* 4 every-nth)) +bits-per-word+)))
                (or-word bits (+ word (floor (+ startmod (* 5 every-nth)) +bits-per-word+)) (ash 1 (mod (+ startmod (* 5 every-nth)) +bits-per-word+)))
                (or-word bits (+ word (floor (+ startmod (* 6 every-nth)) +bits-per-word+)) (ash 1 (mod (+ startmod (* 6 every-nth)) +bits-per-word+)))
                (or-word bits (+ word (floor (+ startmod (* 7 every-nth)) +bits-per-word+)) (ash 1 (mod (+ startmod (* 7 every-nth)) +bits-per-word+)))
             finally (setq i (+ startmod (* word +bits-per-word+)))
        )
        )

       (when *debug* (format t "endloop: [~d .. ~d[~%" i last-excl))
       (loop while (< i last-excl)
             do (set-nth-bit bits i)
                (incf i every-nth))
       ))

    (t
     ; use an unrolled loop to set every every-th bit to 1
     (let* ((i first-incl)
            (every-nth-times-2 (+ every-nth every-nth))
            (every-nth-times-3 (+ every-nth-times-2 every-nth))
            (every-nth-times-4 (+ every-nth-times-3 every-nth))
            (end1 (- last-excl every-nth-times-3)))
       (declare (fixnum i every-nth-times-2 every-nth-times-3 every-nth-times-4 end1))

       (loop while (< i end1)
             do (set-nth-bit bits i)
                (set-nth-bit bits (+ i every-nth))
                (set-nth-bit bits (+ i every-nth-times-2))
                (set-nth-bit bits (+ i every-nth-times-3))
                (incf i every-nth-times-4))

       (loop while (< i last-excl)
             do (set-nth-bit bits i)
                (incf i every-nth)))))))


(defun run-sieve (sieve-state)
  (declare (type sieve-state sieve-state))

  (let* ((rawbits (sieve-state-a sieve-state))
         (sieve-size (sieve-state-maxints sieve-state))
         (sieve-sizeh (ceiling sieve-size 2))
         (factor 0)
         (factorh 1)
         (qh (ceiling (floor (sqrt sieve-size)) 2)))
    (declare (fixnum sieve-size sieve-sizeh factor factorh qh) (type sieve-array-type rawbits))
    (loop do

      (loop for num of-type fixnum
            from factorh
            to qh
            while (nth-bit-set-p rawbits num)
            finally (setq factor (1+ (* num 2)))
                    (setq factorh (1+ num)))

      (when (> factorh qh)
        (return-from run-sieve sieve-state))

      (set-bits rawbits (floor (the fixnum (* factor factor)) 2) sieve-sizeh factor))
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


;#+nil
(let* ((passes 0)
       (start (get-internal-real-time))
       (end (+ start (* internal-time-units-per-second 5)))
       result)
  (declare (fixnum passes))

  (loop while (<= (get-internal-real-time) end)
        do (setq result (run-sieve (create-sieve 1000000)))
           (incf passes))

  (let* ((duration  (/ (- (get-internal-real-time) start) internal-time-units-per-second))
         (avg (/ duration passes)))
    (when *list-to* (list-primes result))
    (format *error-output* "Algorithm: base w/ bitops  Passes: ~d  Time: ~f Avg: ~f ms Count: ~d  Valid: ~A~%"
            passes duration (* 1000 avg) (count-primes result) (validate result))

    (format t "mayerrobert-clb;~d;~f;1;algorithm=base,faithful=yes,bits=1~%" passes duration)))

;(disassemble 'set-bits)


#+nil
(progn
(defparameter *words* 10)
(defparameter *a* (make-array *words* :element-type 'sieve-element-type))

(defparameter *first* 20)
(defparameter *last*  50)
(defparameter *every* 3)

;(defun set-bits (bits first-incl last-excl every-nth)
(set-bits *a* *first* *last* *every*)

(dotimes (i *words*)
  (format t "~2d: ~2d - ~2d: ~8,'0b~%" i (+ +bits-per-word+(* i +bits-per-word+) -1) (* i +bits-per-word+) (aref *a* i)))

(defun tst (start end skip words)
  (format t "tst: ~%first=~d, last=~d, every=~d~%" start end skip)
  (let ((a (make-array words :element-type 'sieve-element-type)))
    (set-bits a start end skip)
    (loop for i from 0 to (1- start)
          do (when (nth-bit-set-p a i)
               (format t "FEHLER: bit ~d ist 1, sollte 0 sein (bit vor start gesetzt)~%" i)))
    (loop for i from start to (1- end)
          do (if (zerop (mod (- i start) skip))
                   (unless (nth-bit-set-p a i) (format t "FEHLER: bit ~d ist 0, sollte 1 sein~%" i))
               (when (nth-bit-set-p a i) (format t "FEHLER: bit ~d ist 1, sollte 0 sein~%" i))))
    (loop for i from end to (1- (* words +bits-per-word+))
          do (when (nth-bit-set-p a i)
               (format t "FEHLER: bit ~d ist 1, sollte 0 sein (bit nach end gesetzt)~%" i)))
    (terpri)))


(let ((*debug* nil))
  (tst *first* *last* *every* 10)
  (tst 1 *last* *every* 10)
  )
)
