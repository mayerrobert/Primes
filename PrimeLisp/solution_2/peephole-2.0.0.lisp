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
(defpattern "sar + sar -> sar" ((sar) (sar)) (stmt next)
  (binding* (((size1 dst1 src1) (parse-2-operands stmt))
             ((size2 dst2 src2) (parse-2-operands next)))
    (when (and (gpr-tn-p dst1)
               (location= dst2 dst1)
               (or (and (eq size1 :qword)
                        (eq size2 :qword))
                   (and (eq size1 :dword)
                        (eq size2 :dword)))
               (typep src1 '(signed-byte 32))
               (typep src2 '(signed-byte 32)))
      (setf (stmt-operands next)
            `(,size2 ,dst2 ,(+ src1 src2)))                      ; SBCL 2.0.0 style
;            `(,(encode-size-prefix size2) ,dst2 ,(+ src1 src2))) ; SBCL 2.1.7 style
      (add-stmt-labels next (stmt-labels stmt))
      (delete-stmt stmt)
      next)))
