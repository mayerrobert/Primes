
(in-package "SB-VM")

; from SBCL 2.0.0 sbcl\share\src\src\compiler\x86-64\array.lisp:268

#+nil
(define-vop (data-vector-ref-with-offset/simple-bit-vector)
  (:translate data-vector-ref-with-offset)
  (:policy :fast-safe)
  (:args (object :scs (descriptor-reg))
         (index :scs (unsigned-reg)))
  (:info offset)
  (:ignore offset)
  (:arg-types simple-bit-vector positive-fixnum (:constant (integer 0 0)))
  (:results (result :scs (any-reg)))
  (:result-types positive-fixnum)
  (:generator 4
    (inst bt (ea (- (* vector-data-offset n-word-bytes) other-pointer-lowtag)
                 object) index)
    (inst sbb :dword result result)
    (inst and :dword result (fixnumize 1))))



; from SBCL 2.0.0 sbcl\share\src\src\compiler\x86-64\array.lisp:284

#+nil
(macrolet ((def-small-data-vector-frobs (type bits)
             (let* ((elements-per-word (floor n-word-bits bits))
                    (bit-shift (1- (integer-length elements-per-word))))
    `(progn
      ,@(unless (= bits 1)
       `((define-vop (,(symbolicate 'data-vector-ref-with-offset/ type))
         (:note "inline array access")
         (:translate data-vector-ref-with-offset)
         (:policy :fast-safe)
         (:args (object :scs (descriptor-reg))
                (index :scs (unsigned-reg)))
         (:info offset)
         (:arg-types ,type positive-fixnum (:constant (integer 0 0)))
         (:results (result :scs (unsigned-reg) :from (:argument 0)))
         (:result-types positive-fixnum)
         (:temporary (:sc unsigned-reg :offset ecx-offset) ecx)
         (:generator 20
           (aver (zerop offset))
           (move ecx index)
           (inst shr ecx ,bit-shift)
           (inst mov result
                 (ea (- (* vector-data-offset n-word-bytes) other-pointer-lowtag)
                     object ecx n-word-bytes))
           (move ecx index)
           ;; We used to mask ECX for all values of BITS, but since
           ;; Intel's documentation says that the chip will mask shift
           ;; and rotate counts by 63 automatically, we can safely move
           ;; the masking operation under the protection of this UNLESS
           ;; in the bit-vector case.  --njf, 2006-07-14
           ,@(unless (= bits 1)
               `((inst and ecx ,(1- elements-per-word))
                 (inst shl ecx ,(1- (integer-length bits)))))
           (inst shr result :cl)
           (inst and result ,(1- (ash 1 bits)))))
       (define-vop (,(symbolicate 'data-vector-ref-with-offset/ type "-C"))
         (:translate data-vector-ref-with-offset)
         (:policy :fast-safe)
         (:args (object :scs (descriptor-reg)))
         (:arg-types ,type (:constant low-index) (:constant (integer 0 0)))
         (:info index offset)
         (:results (result :scs (unsigned-reg)))
         (:result-types positive-fixnum)
         (:generator 15
           (aver (zerop offset))
           (multiple-value-bind (word extra) (floor index ,elements-per-word)
             (loadw result object (+ word vector-data-offset)
                    other-pointer-lowtag)
             (unless (zerop extra)
               (inst shr result (* extra ,bits)))
             (unless (= extra ,(1- elements-per-word))
               (inst and result ,(1- (ash 1 bits)))))))))
       (define-vop (,(symbolicate 'data-vector-set-with-offset/ type))
         (:note "inline array store")
         (:translate data-vector-set-with-offset)
         (:policy :fast-safe)
         (:args (object :scs (descriptor-reg))
                (index :scs (unsigned-reg) :target ecx)
                (value :scs (unsigned-reg immediate) :target result))
         (:info offset)
         (:arg-types ,type positive-fixnum (:constant (integer 0 0))
                     positive-fixnum)
         (:results (result :scs (unsigned-reg)))
         (:result-types positive-fixnum)
         (:temporary (:sc unsigned-reg) word-index)
         (:temporary (:sc unsigned-reg) old)
         (:temporary (:sc unsigned-reg :offset ecx-offset) ecx)
         (:generator 25
           (aver (zerop offset))
           (move word-index index)
           (inst shr word-index ,bit-shift)
           (inst mov old
                 (ea (- (* vector-data-offset n-word-bytes) other-pointer-lowtag)
                     object word-index n-word-bytes))
           (move ecx index)
           ;; We used to mask ECX for all values of BITS, but since
           ;; Intel's documentation says that the chip will mask shift
           ;; and rotate counts by 63 automatically, we can safely move
           ;; the masking operation under the protection of this UNLESS
           ;; in the bit-vector case.  --njf, 2006-07-14
           ,@(unless (= bits 1)
               `((inst and ecx ,(1- elements-per-word))
                 (inst shl ecx ,(1- (integer-length bits)))))
           (inst ror old :cl)
           (unless (and (sc-is value immediate)
                        (= (tn-value value) ,(1- (ash 1 bits))))
             (inst and old ,(lognot (1- (ash 1 bits)))))
           (sc-case value
             (immediate
              (unless (zerop (tn-value value))
                (inst or old (logand (tn-value value) ,(1- (ash 1 bits))))))
             (unsigned-reg
              (inst or old value)))
           (inst rol old :cl)
           (inst mov (ea (- (* vector-data-offset n-word-bytes) other-pointer-lowtag)
                         object word-index n-word-bytes)
                 old)
           (sc-case value
             (immediate
              (inst mov result (tn-value value)))
             (unsigned-reg
              (move result value)))))
       (define-vop (,(symbolicate 'data-vector-set-with-offset/ type "-C"))
         (:translate data-vector-set-with-offset)
         (:policy :fast-safe)
         (:args (object :scs (descriptor-reg))
                (value :scs (unsigned-reg immediate) :target result))
         (:arg-types ,type (:constant low-index)
                     (:constant (integer 0 0)) positive-fixnum)
         (:temporary (:sc unsigned-reg) mask-tn)
         (:info index offset)
         (:results (result :scs (unsigned-reg)))
         (:result-types positive-fixnum)
         (:temporary (:sc unsigned-reg :to (:result 0)) old)
         (:generator 20
           (aver (zerop offset))
           (multiple-value-bind (word extra) (floor index ,elements-per-word)
             (inst mov old
                   (ea (- (* (+ word vector-data-offset) n-word-bytes)
                          other-pointer-lowtag)
                       object))
             (sc-case value
               (immediate
                (let* ((value (tn-value value))
                       (mask ,(1- (ash 1 bits)))
                       (shift (* extra ,bits)))
                  (unless (= value mask)
                    (inst mov mask-tn (ldb (byte 64 0)
                                           (lognot (ash mask shift))))
                    (inst and old mask-tn))
                  (unless (zerop value)
                    (inst mov mask-tn (ash value shift))
                    (inst or old mask-tn))))
               (unsigned-reg
                (let ((shift (* extra ,bits)))
                  (unless (zerop shift)
                    (inst ror old shift))
                  (inst mov mask-tn (lognot ,(1- (ash 1 bits))))
                  (inst and old mask-tn)
                  (inst or old value)
                  (unless (zerop shift)
                    (inst rol old shift)))))
             (inst mov (ea (- (* (+ word vector-data-offset) n-word-bytes)
                              other-pointer-lowtag)
                           object)
                   old)
             (sc-case value
               (immediate
                (inst mov result (tn-value value)))
               (unsigned-reg
                (move result value))))))))))
  (def-small-data-vector-frobs simple-bit-vector 1)
  (def-small-data-vector-frobs simple-array-unsigned-byte-2 2)
  (def-small-data-vector-frobs simple-array-unsigned-byte-4 4))

(let* ((elements-per-word (floor n-word-bits 1))
       (bit-shift (1- (integer-length elements-per-word))))
  (define-vop (data-vector-set-with-offset/simple-bit-vector)
    (:note "inline array store")
    (:translate data-vector-set-with-offset)
    (:policy :fast-safe)
    (:args (object :scs (descriptor-reg))
           (index :scs (unsigned-reg) :target ecx)
           (value :scs (unsigned-reg immediate) :target result))
    (:info offset)
    (:arg-types simple-bit-vector positive-fixnum (:constant (integer 0 0))
                positive-fixnum)
    (:results (result :scs (unsigned-reg)))
    (:result-types positive-fixnum)
    (:temporary (:sc unsigned-reg) word-index)
    (:temporary (:sc unsigned-reg) old)
    (:temporary (:sc unsigned-reg :offset ecx-offset) ecx)
    (:generator 24
      (aver (zerop offset))
      (move word-index index)
      (inst shr word-index bit-shift)
      (inst mov old
            (ea (- (* vector-data-offset n-word-bytes) other-pointer-lowtag)
                object word-index n-word-bytes))
      (move ecx index)
      ;; We used to mask ECX for all values of BITS, but since
      ;; Intel's documentation says that the chip will mask shift
      ;; and rotate counts by 63 automatically, we can safely move
      ;; the masking operation under the protection of this UNLESS
      ;; in the bit-vector case.  --njf, 2006-07-14
      ;,@(unless (= 1 1)
      ;    `((inst and ecx ,(1- elements-per-word))
      ;      (inst shl ecx ,(1- (integer-length 1)))))
      (inst ror old :cl)
      (unless (and (sc-is value immediate)
                   (= (tn-value value) (1- (ash 1 1))))
        (inst and old (lognot (1- (ash 1 1)))))
      (sc-case value
        (immediate
         (unless (zerop (tn-value value))
           (inst or old (logand (tn-value value) (1- (ash 1 1))))))
        (unsigned-reg
         (inst or old value)))
      (inst rol old :cl)
      (inst mov (ea (- (* vector-data-offset n-word-bytes) other-pointer-lowtag)
                    object word-index n-word-bytes)
            old)
      (sc-case value
        (immediate
         (inst mov result (tn-value value)))
        (unsigned-reg
         (move result value))))))


(in-package "CL-USER")

(declaim (optimize speed (safety 0)))

(disassemble (lambda (a n)
               (declare (type simple-bit-vector a) (fixnum n))
               (setf (aref a n) 1)))
