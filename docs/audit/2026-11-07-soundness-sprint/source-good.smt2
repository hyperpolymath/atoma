; atoma.source.u8.v1 source-blake3:ec82c5b0bd32ac560b4b984fd7c8d88f8e0c1f1dcabee9ede457132c1b7e5022
; Warrant only: frontend and compiler refinement remain trusted
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (not (= (bvadd x (_ bv1 8)) (bvadd x (_ bv1 8)))))
(check-sat)
