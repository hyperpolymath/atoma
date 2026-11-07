; atoma.source.u8.v1 source-blake3:bd2dd1c4c6b45f4ba3f58ece20f737ea9121bde5061f64b593b2e039d5e4d041
; Warrant only: frontend and compiler refinement remain trusted
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (not (= (bvadd x (_ bv1 8)) (bvadd x (_ bv1 8)))))
(check-sat)
