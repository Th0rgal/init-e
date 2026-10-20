import InitECandidate.Runtime.OriginalRuntimeCode
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def attemptRejectHandler (tag : BitVec 64) : ProgHOL 64 :=
  .seq (.shMemStore .op8 (.op .add [.const 2688614400#64,.const 70#64]) (.var .local (ofString "e")))
    (.raise (ofString "Fail") (.const tag))
def attemptLayerBody (callee exceptionId : MlS) (tag : BitVec 64) : ProgHOL 64 :=
  .dec (ofString "e") .one (.const 0#64)
    (.seq (.call (some (none,some (exceptionId,ofString "e",attemptRejectHandler tag))) callee
      [.var .local (ofString "si")]) (.return (.const 0#64)))
def verifyAttemptHandler : ProgHOL 64 :=
  .seq (.assign .local (ofString "ok") (.const 0#64))
    (.assign .global (ofString "fail_code") (.var .local (ofString "e")))
def verifyAttemptBody : ProgHOL 64 :=
  .dec (ofString "e") .one (.const 0#64) (.dec (ofString "ok") .one (.const 1#64)
    (.seq (.call (some (none,some (ofString "Fail",ofString "e",verifyAttemptHandler)))
      (ofString "attempt_l7") [.var .local (ofString "si")]) (.return (.var .local (ofString "ok")))))
theorem source_attempt_l1_body : sourceFunctionBody Guest.guestFn_attempt_l1 =
    attemptLayerBody (ofString "run_attempt") (ofString "BlockErr") 1#64 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_attempt_l1,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl
#print axioms source_attempt_l1_body
theorem source_attempt_l2_body : sourceFunctionBody Guest.guestFn_attempt_l2 =
    attemptLayerBody (ofString "attempt_l1") (ofString "HdrErr") 2#64 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_attempt_l2,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl
#print axioms source_attempt_l2_body
theorem source_attempt_l3_body : sourceFunctionBody Guest.guestFn_attempt_l3 =
    attemptLayerBody (ofString "attempt_l2") (ofString "RlpErr") 3#64 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_attempt_l3,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl
#print axioms source_attempt_l3_body
theorem source_attempt_l4_body : sourceFunctionBody Guest.guestFn_attempt_l4 =
    attemptLayerBody (ofString "attempt_l3") (ofString "MptErr") 4#64 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_attempt_l4,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl
#print axioms source_attempt_l4_body
theorem source_attempt_l5_body : sourceFunctionBody Guest.guestFn_attempt_l5 =
    attemptLayerBody (ofString "attempt_l4") (ofString "StateErr") 5#64 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_attempt_l5,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl
#print axioms source_attempt_l5_body
theorem source_attempt_l6_body : sourceFunctionBody Guest.guestFn_attempt_l6 =
    attemptLayerBody (ofString "attempt_l5") (ofString "TxErr") 6#64 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_attempt_l6,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl
#print axioms source_attempt_l6_body
theorem source_attempt_l7_body : sourceFunctionBody Guest.guestFn_attempt_l7 =
    attemptLayerBody (ofString "attempt_l6") (ofString "EvmErr") 7#64 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_attempt_l7,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl
#print axioms source_attempt_l7_body
theorem source_verify_attempt_body : sourceFunctionBody Guest.guestFn_verify_stateless_new_payload = verifyAttemptBody := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_verify_stateless_new_payload,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none]
  rfl
#print axioms source_verify_attempt_body
end InitECandidate.Runtime
