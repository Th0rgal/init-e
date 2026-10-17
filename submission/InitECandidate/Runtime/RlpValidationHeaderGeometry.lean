import InitECandidate.Runtime.RlpValidationHeaderCallFrame
import InitECandidate.Runtime.RlpHeaderSizedGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original validator header-call completion exposes the actual parsed fields,
parent/nested cursor geometry and unchanged caller memory for its continuation. -/
theorem evaluate_rlpValidation_header_geometry {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (ordered : position.toNat ≤ stop.toNat) (inputBound : (stop - position).toNat + 9 < 2^64)
    (code : state.code = originalRuntimeCode) (ticks : 12 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpValidationHeaderCall = (none,post)) :
    ∃ (header payload kind : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      (kind = 0 ∨ kind = 1) ∧
      position.toNat < (position + header + payload).toNat ∧
      (position + header + payload).toNat ≤ stop.toNat ∧
      (kind = 1 → position.toNat < (position + header).toNat ∧
        (position + header).toNat ≤ (position + header + payload).toNat) ∧
      ready.locals = state.locals ∧ ready.memory = state.memory ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString "h")
        (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) ready)
        rlpValidationHeaderContinuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (ofString "h",state.locals.lookup (ofString "h"))} := by
  obtain ⟨value,ready,output,valid,locals,memory,tail,restored⟩ :=
    evaluate_rlpValidation_header_call_frame state post position stop positionLocal stopLocal code ticks run
  obtain ⟨header,payload,kind,shape,_,_,_⟩ := valid.2
  subst value
  have fields := valid.fields header payload kind (stop - position)
  have cursor := valid.cursor position stop header payload kind ordered
  refine ⟨header,payload,kind,ready,output,fields.1,cursor.1,cursor.2,?_,locals,memory,tail,restored⟩
  intro list
  subst kind
  have geometry := valid.list_geometry position stop header payload ordered inputBound
  exact ⟨geometry.1,geometry.2.1⟩

#print axioms evaluate_rlpValidation_header_geometry
end InitECandidate.Runtime
