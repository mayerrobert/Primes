
(declaim
  (optimize (speed 3) (safety 0) (debug 0) (space 0))

  (inline shl)
  (inline bit-pattern)
  (inline set-nth-bit)
)


(defconstant +bits-per-word+ 8)

(deftype sieve-element-type ()
  `(unsigned-byte ,+bits-per-word+))

(deftype sieve-array-type ()
  `(simple-array sieve-element-type 1))

(deftype sieve-bitpos-type ()
  `(integer 0 ,(1- +bits-per-word+)))


; see https://rosettacode.org/wiki/Bitwise_operations#Common_Lisp
(defun shl (x bits)
  "Compute bitwise left shift of x by 'bits' bits, represented on 'width' bits"
  (declare (type sieve-element-type x) (type sieve-bitpos-type bits))
  (logand (ash x bits)
          (1- (ash 1 +bits-per-word+))))

(defun shr (x bits)
  "Compute bitwise right shift of x by 'bits' bits, represented on 'width' bits"
  (declare (type sieve-element-type x) (type sieve-bitpos-type bits))
  (logand (ash x (- bits))
          (1- (ash 1 +bits-per-word+))))

(defun rotl (x bits)
  "Compute bitwise left rotation of x by 'bits' bits, represented on 'width' bits"
  (declare (type sieve-element-type x) (type sieve-bitpos-type bits))
  (logior (logand (ash x (mod bits +bits-per-word+))
                  (1- (ash 1 +bits-per-word+)))
          (logand (ash x (- (- +bits-per-word+ (mod bits +bits-per-word+))))
                  (1- (ash 1 +bits-per-word+)))))

(defun rotr (x bits)
  "Compute bitwise right rotation of x by 'bits' bits, represented on 'width' bits"
  (declare (type sieve-element-type x) (type sieve-bitpos-type bits))
  (logior (logand (ash x (- (mod bits +bits-per-word+)))
                  (1- (ash 1 +bits-per-word+)))
          (logand (ash x (- +bits-per-word+ (mod bits +bits-per-word+)))
                  (1- (ash 1 +bits-per-word+)))))


(defun set-nth-bit (a n)
  (declare (type sieve-array-type a)
           (type fixnum n))
  (multiple-value-bind (q r) (floor n +bits-per-word+)
    (declare (fixnum q r))
    (setf #1=(aref a q)
         (logior #1# (expt 2 r)))) 0)


(defun bit-pattern (n)
  (declare (fixnum n))
  (logand (1- (ash 1 +bits-per-word+))
    (case  n
      (2  #b0101010101010101010101010101010101010101010101010101010101010101)
      (3  #b1001001001001001001001001001001001001001001001001001001001001001)
      (4  #b0001000100010001000100010001000100010001000100010001000100010001)
      (5  #b0001000010000100001000010000100001000010000100001000010000100001)
      (6  #b0001000001000001000001000001000001000001000001000001000001000001)
      (7  #b1000000100000010000001000000100000010000001000000100000010000001)
      (8  #b0000000100000001000000010000000100000001000000010000000100000001)
      (9  #b0100000001000000001000000001000000001000000001000000001000000001)
      (10 #b0001000000000100000000010000000001000000000100000000010000000001)
      (11 #b0000000010000000000100000000001000000000010000000000100000000001)
      (12 #b0001000000000001000000000001000000000001000000000001000000000001)
      (13 #b0000000000010000000000001000000000000100000000000010000000000001)
      (14 #b0000000100000000000001000000000000010000000000000100000000000001)
      (15 #b0001000000000000001000000000000001000000000000001000000000000001)
      (16 #b0000000000000001000000000000000100000000000000010000000000000001)
      (17 #b0000000000001000000000000000010000000000000000100000000000000001)
      (18 #b0000000001000000000000000001000000000000000001000000000000000001)
      (19 #b0000001000000000000000000100000000000000000010000000000000000001)
      (20 #b0001000000000000000000010000000000000000000100000000000000000001)
      )))


(defun set-bits (bits first-incl last-excl every-nth)
  (declare (type fixnum first-incl last-excl every-nth)
           (type sieve-array-type bits))
  (if (<= every-nth 20)

        (let* ((pattern (bit-pattern every-nth)) (tmp 0) (shift 0) (total 0))
          (declare (type sieve-element-type pattern) (fixnum tmp shift total))

          ; set first word and prepare pattern
          (multiple-value-bind (q r) (floor first-incl +bits-per-word+)
            (when (< last-excl +bits-per-word+)
              (setf (aref bits q) (logior (aref bits q)
                                          (logand (shl pattern r) (1- (shl 1 last-excl)))))
              (return-from set-bits nil))
            (setf (aref bits q) (logior (aref bits q) (shl pattern r)))
            (setq total (mod r every-nth))
            (setq pattern (shl pattern total))
            (setq shift (- every-nth (mod +bits-per-word+ every-nth)))
            )

          (loop for num of-type fixnum
                from (1+ (floor first-incl +bits-per-word+))
                to (1- (floor last-excl +bits-per-word+))
                do ; loop over [2nd to last-excl[
                  (if (>= (setq total (+ total shift)) every-nth)
                        (progn
                          (setq pattern (logior (shl pattern shift) (shl 1 (the fixnum (- total every-nth)))))
                          (setq total (- total every-nth)))
                    (setq pattern (shl pattern shift)))

                  (setf (aref bits num) (logior (aref bits num) pattern))

                finally ; set last word
                  (setq tmp (- last-excl (* num +bits-per-word+)))
                  (when (> tmp 0)
                    (if (>= (setq total (+ total shift)) every-nth)
                          (setq pattern (logior (shl pattern shift) (shl 1 (the fixnum (- total every-nth)))))
                      (setq pattern (shl pattern shift)))

                    (setq pattern (logand pattern (1- (shl 1 tmp))))

                    (setf (aref bits num) (logior (aref bits num) pattern)))
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
  (let ((first 10)
        (last 13)
        (bits (make-array 4 :element-type 'sieve-element-type)))
    (format t "first=~d, last=~d, every=~d~%" first last every)
    (set-bits bits first last every)
    (format t "*****~%")
    (loop for i from 0 to 3 do
      (format t "~d ~8,'0b~%" i (aref bits i)))))

(disassemble 'set-bits)
