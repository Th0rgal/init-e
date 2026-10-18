import InitECandidate.Runtime.SszCheckOffsetsCallBound
import InitECandidate.Runtime.PayloadStoreTailBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def payloadOffsetCheckArguments : List (ExpHOL 64) :=
  [.var .global (ofString "ssz_offs"),.const 4,.const 540,.var .local (ofString "len")]

def payloadOffsetCheckCall : ProgHOL 64 :=
  .call (some (none,none)) (ofString "ssz_check_offsets") payloadOffsetCheckArguments

theorem source_payload_offset_check : payloadAt 12 = .seq payloadOffsetCheckCall (payloadAt 13) := by
  simp only [payloadOffsetCheckCall,payloadOffsetCheckArguments,payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original payload offset check costs at most ten ticks. No readable
or valid offset-array premise is needed: rejected inputs are covered too. -/
theorem evaluate_payload_offset_check_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (offsets length : BitVec 64)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (budget : 10 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state payloadOffsetCheckCall
    state.clock ≤ evaluated.2.clock + 10 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      payloadOffsetCheckArguments =
      some [.val (.word offsets),.val (.word (4 : BitVec 64)),.val (.word (540 : BitVec 64)),.val (.word length)] := by
    simp [payloadOffsetCheckArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atOffsets,atLength]
  exact evaluate_sszCheckOffsets_call_bounded state none payloadOffsetCheckArguments offsets 4 540 length
    args code (by decide) budget

#print axioms source_payload_offset_check
#print axioms evaluate_payload_offset_check_call_bounded
end InitECandidate.Runtime
