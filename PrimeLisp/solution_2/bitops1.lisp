;#+64-bit (defconstant +bits-per-word+ 64)
;#-64-bit (defconstant +bits-per-word+ 32)

(defconstant +bits-per-word+ 8)

(deftype sieve-element-type ()
  `(unsigned-byte ,+bits-per-word+))

(deftype sieve-array-type ()
  `(simple-array sieve-element-type 1))


; see https://rosettacode.org/wiki/Bitwise_operations#Common_Lisp
(defun shl (x bits)
  "Compute bitwise left shift of x by 'bits' bits, represented on 'width' bits"
  (declare (type (unsigned-byte 64) bits))
  (logand (ash x bits)
          (1- (ash 1 +bits-per-word+))))

(defun shr (x bits)
  "Compute bitwise right shift of x by 'bits' bits, represented on 'width' bits"
  (declare (type (unsigned-byte 64) bits))
  (logand (ash x (- bits))
          (1- (ash 1 +bits-per-word+))))

(defun rotl (x bits)
  "Compute bitwise left rotation of x by 'bits' bits, represented on 'width' bits"
  (declare (type (unsigned-byte 64) bits))
  (logior (logand (ash x (mod bits +bits-per-word+))
                  (1- (ash 1 +bits-per-word+)))
          (logand (ash x (- (- +bits-per-word+ (mod bits +bits-per-word+))))
                  (1- (ash 1 +bits-per-word+)))))

(defun rotr (x bits)
  "Compute bitwise right rotation of x by 'bits' bits, represented on 'width' bits"
  (declare (type (unsigned-byte 64) bits))
  (logior (logand (ash x (- (mod bits +bits-per-word+)))
                  (1- (ash 1 +bits-per-word+)))
          (logand (ash x (- +bits-per-word+ (mod bits +bits-per-word+)))
                  (1- (ash 1 +bits-per-word+)))))


(defun bit-pattern (n)
  (case  n
    (2 #b0101010101010101010101010101010101010101010101010101010101010101)
    (3 #b1001001001001001001001001001001001001001001001001001001001001001)
    (4 #b0001000100010001000100010001000100010001000100010001000100010001)
    (5 #b0001000010000100001000010000100001000010000100001000010000100001)
    (6 #b0001000001000001000001000001000001000001000001000001000001000001)
    (7 #b1000000100000010000001000000100000010000001000000100000010000001)
    (8 #b0000000100000001000000010000000100000001000000010000000100000001)))


(defun set-bits (bits first-incl last-excl every-nth)
  (declare (type fixnum first-incl last-excl every-nth)
           (type sieve-array-type bits))
  (if (< every-nth 9)

        (let* ((pattern (bit-pattern every-nth)) (tmp 0) (lastnum 0) (shift 0) (total 0))
          (declare (type (unsigned-byte 64) pattern) (fixnum tmp lastnum shift))

          ; set first word and prepare pattern
          (multiple-value-bind (q r) (floor first-incl +bits-per-word+)
            (setf (aref bits q) (logior (aref bits q) (shl pattern r)))
            (setq total (mod r every-nth))
            (setq pattern (shl pattern total))
            (setq shift (- every-nth (mod +bits-per-word+ every-nth)))
            )

          (loop for num of-type fixnum
                from (1+ (floor first-incl +bits-per-word+))
                to (1- (floor last-excl +bits-per-word+))
                do ; loop over [2nd to last-excl[
                  (setq pattern (shl pattern shift))

                  (incf total shift)
                  (when (>= total every-nth)
                    ;(format t "~d: ~d ~d ~8,'0b ~%" num total (- total every-nth) (ash 1 (- total every-nth)))
                    (setq pattern (logior pattern (ash 1 (- total every-nth))))
                    (decf total every-nth))

                  (setf (aref bits num) (logior (aref bits num) pattern))

                finally ; set last word
                  (setq pattern (shl pattern shift))
             
                  (incf total shift)
                  (when (>= total every-nth)
                    ;(format t "~d: ~d ~d ~8,'0b ~%" num total (- total every-nth) (ash 1 (- total every-nth)))
                    (setq pattern (logior pattern (ash 1 (- total every-nth))))
                    (decf total every-nth))

                  (setq tmp (- last-excl (* num +bits-per-word+)))
                  (format t "num=~d tmp=~d mask=~8,'0b~%" num tmp (1- (ash 1 tmp)))
                  (setq pattern (logand pattern (1- (ash 1 tmp))))

                  (setf (aref bits num) (logior (aref bits num) pattern))
            ))

    (loop for num of-type fixnum
          from first-incl
          to (1- last-excl)
          by every-nth
          do
      (set-nth-bit bits num))))


#+nil
(defun set-bits (bits first-incl last-excl every-nth)
  (declare (type fixnum first-incl last-excl every-nth)
           (type sieve-array-type bits))
  (if (< every-nth +bits-per-word+)

        (let* ((prev-idx (floor first-incl +bits-per-word+))
               (prev (aref bits prev-idx)))
          (declare (fixnum prev-idx prev))
          (loop for num of-type fixnum
                from first-incl
                to (1- last-excl)
                by every-nth
                do
            (multiple-value-bind (q r) (floor num +bits-per-word+)
              (declare (fixnum q r))
              (when (> q prev-idx)
                (setf (aref bits prev-idx) prev)
                (setq prev (aref bits q))
                (setq prev-idx q))
              (setq prev (logior prev (expt 2 r)))))
          (setf (aref bits prev-idx) prev))

    (loop for num of-type fixnum
          from first-incl
          to (1- last-excl)
          by every-nth
          do
      (set-nth-bit bits num))))


#-nil
(dolist (every '(2 3 4 5))
  (let ((first 3)
        (last 35)
        (bits (make-array 5 :element-type 'sieve-element-type)))
    (format t "first=~d, last=~d, every=~d~%" first last every)
    (set-bits bits first last every)
    (format t "*****~%")
    (loop for i from 0 to 4 do
      (format t "~d ~8,'0b~%" i (aref bits i)))))
