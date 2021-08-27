(in-package "SB-X86-64-ASM")

;;;; "AND r, imm1" + "AND r, imm2" -> "AND r, (imm1 & imm2)"
;(defpattern "and + and -> and" ((and) (and)) (stmt next)
;  (binding* (((size1 dst1 src1) (parse-2-operands stmt))
;             ((size2 dst2 src2) (parse-2-operands next)))
;    (when (and (gpr-tn-p dst1)
;               (location= dst2 dst1)
;               (member size1 '(:qword :dword))
;               (typep src1 '(signed-byte 32))
;               (member size2 '(:dword :qword))
;               (typep src2 '(signed-byte 32)))
;      (setf (stmt-operands next)
;            `(,(smaller-of size1 size2) ,dst2 ,(logand src1 src2)))
;      (add-stmt-labels next (stmt-labels stmt))
;      (delete-stmt stmt)
;      next)))


;;; "SAR r, imm1" + "SAR r, imm2" -> "SAR r, (imm1 + imm2)"
;;; this assumes that imm1 and imm2 are both positive
;;;
;;; modeled after the existing pattern
;;; "AND r, imm1" + "AND r, imm2" -> "AND r, (imm1 & imm2)"
;;;
;;; the optimization is only applied when
;;; - both operands are of the same size
;;; - the combined-shift-amount < 64 for qword args or 
;;; - the combined-shift-amount < 32 for dword args 
(defpattern "sar + sar -> sar" (#1=(sar sal shr shl ror rol) #1#) (stmt next)
  (binding* (((size1 dst1 src1) (parse-2-operands stmt))
             ((size2 dst2 src2) (parse-2-operands next))
             (combined-shift-amount (+ src1 src2)))
    (flet ((compatible (first second)
             (or (eq first second)
                 ;; SHR followed by SAR is ok because the SHR will shift in
                 ;; at least one 0 bit, and the SAR becomes equivalent to SHR.
                 (and (eq first 'shr) (eq second 'sar)))))
      (when (and (gpr-tn-p dst1)
                 (location= dst2 dst1)
                 (eq size1 size2)
                 (compatible (stmt-mnemonic stmt) (stmt-mnemonic next))
                 (/= 1 src2) ; various shift by one instructions affect CF/OF flag -> don't optimize that away, see https://sourceforge.net/p/sbcl/mailman/message/37339851/
                             ; also see src\compiler\x86-64\move.lisp for move vops that use shl 1/ sar 1 and then use the flags
                 (or (and (eq size1 :qword) (< combined-shift-amount 64))
                     (and (eq size1 :dword) (< combined-shift-amount 32)))
                 (typep src1 '(signed-byte 32))
                 (typep src2 '(signed-byte 32)))
;        (format t "********** ~A **********~%" (stmt-mnemonic stmt))
        (setf (stmt-operands next)
;              `(,size2 ,dst2 ,combined-shift-amount))                      ; SBCL 2.0.0 style
              `(,(encode-size-prefix size2) ,dst2 ,combined-shift-amount)) ; SBCL 2.1.7 style
        (add-stmt-labels next (stmt-labels stmt))
        (delete-stmt stmt)
        next))))
