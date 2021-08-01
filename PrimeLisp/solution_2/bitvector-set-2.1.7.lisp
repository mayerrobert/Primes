; change the way "simple-bitvector-set immediate" is compiled
; intended for SBCL 2.1.7

(in-package "SB-VM")


#+nil
; copied from SBCL 2.1.7 sbcl\share\src\src\compiler\x86-64\array.lisp:440
(define-vop (data-vector-set-with-offset/simple-bit-vector)
  (:translate data-vector-set-with-offset)
  (:policy :fast-safe)
  ;; Arg order is (VECTOR INDEX ADDEND VALUE)
  (:arg-types simple-bit-vector positive-fixnum (:constant (eql 0)) positive-fixnum)
  (:args (bv :scs (descriptor-reg))
         (index :scs (unsigned-reg immediate))
         (value :scs (immediate any-reg signed-reg unsigned-reg control-stack
                      signed-stack unsigned-stack)))
  (:info addend)
  (:ignore addend)
  (:generator 6
    (unpoison-element bv index)
    (when (sc-is value immediate)
      (ecase (tn-value value)
        (1 (emit-sbit-op 'bts bv index))
        (0 (emit-sbit-op 'btr bv index)))
      (return-from data-vector-set-with-offset/simple-bit-vector))
    (inst test :byte value
          (if (sc-is value control-stack signed-stack unsigned-stack) #xff value))
    (inst jmp :z ZERO)
    (emit-sbit-op 'bts bv index)
    (inst jmp OUT)
    ZERO
    (emit-sbit-op 'btr bv index)
    OUT))


(let* ((elements-per-word (floor n-word-bits 1))
       (bit-shift (1- (integer-length elements-per-word))))
(define-vop (data-vector-set-with-offset/simple-bit-vector)
  (:translate data-vector-set-with-offset)
  (:policy :fast-safe)
  ;; Arg order is (VECTOR INDEX ADDEND VALUE)
  (:arg-types simple-bit-vector positive-fixnum (:constant (eql 0)) positive-fixnum)
  (:args (bv :scs (descriptor-reg))
         (index :scs (unsigned-reg immediate))
         (value :scs (immediate any-reg signed-reg unsigned-reg control-stack
                      signed-stack unsigned-stack)))
  (:info addend)
  (:ignore addend)
  (:temporary (:sc unsigned-reg) word-index)
  (:temporary (:sc unsigned-reg) old)
  (:temporary (:sc unsigned-reg :offset rcx-offset) ecx)
  (:generator 5
    (unpoison-element bv index)
    (when (sc-is value immediate)

      (move word-index index)
      (inst shr word-index bit-shift)
      (move ecx index)

      (when (zerop (tn-value value))
        ; clear bit
        (inst mov old (lognot 1))
        (inst rol old :cl)
        (inst and (ea (- (* vector-data-offset n-word-bytes) other-pointer-lowtag)
                      bv word-index n-word-bytes)
            old))

      (unless (zerop (tn-value value))
        ; set bit
        (inst mov old 1)
        (inst rol old :cl)
        (inst or (ea (- (* vector-data-offset n-word-bytes) other-pointer-lowtag)
                     bv word-index n-word-bytes)
            old))

      ;(inst mov result (tn-value value))
      (return-from data-vector-set-with-offset/simple-bit-vector))

    (inst test :byte value
          (if (sc-is value control-stack signed-stack unsigned-stack) #xff value))
    (inst jmp :z ZERO)
    (emit-sbit-op 'bts bv index)
    (inst jmp OUT)
    ZERO
    (emit-sbit-op 'btr bv index)
    OUT)))
