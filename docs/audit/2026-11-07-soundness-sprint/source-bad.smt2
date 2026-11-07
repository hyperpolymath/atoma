; atoma.source.u8.v1 source-blake3:6a241b52f5295b6aba2a2aa750b37c4901b04d4d517a3f9bc746999bbaf6712e
; Warrant only: frontend and compiler refinement remain trusted
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (not (= (bvadd x (_ bv2 8)) (bvadd x (_ bv1 8)))))
(check-sat)
