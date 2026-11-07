; atoma.source.u8.v1 source-blake3:d754072afcf80eda1a465d6195729788b60ed52e28863bed6df57118ba081e86
; Warrant only: frontend and compiler refinement remain trusted
(set-logic QF_BV)
(declare-fun x () (_ BitVec 8))
(assert (not (= (bvadd x (_ bv2 8)) (bvadd x (_ bv1 8)))))
(check-sat)
