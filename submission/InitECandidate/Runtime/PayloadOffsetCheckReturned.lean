import InitECandidate.Runtime.PayloadOffsetCheckCallBound
import InitECandidate.Runtime.SszCheckOffsetsCallReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful payload offset check validates all four entries and fixes
the first offset at 540, while retaining the complete caller memory frame. -/
theorem payload_offset_check_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (offsets length : BitVec 64)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state payloadOffsetCheckCall = (none,post)) :
    state.memaddrs offsets ∧ memWord state.memory offsets = 540 ∧
      (∀ k : BitVec 64, k.toNat < 4 → SszOffsetOK state offsets 540 length k) ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.locals = state.locals := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      payloadOffsetCheckArguments =
      some [.val (.word offsets),.val (.word (4 : BitVec 64)),.val (.word (540 : BitVec 64)),.val (.word length)] := by
    simp [payloadOffsetCheckArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atOffsets,atLength]
  obtain ⟨contract,memory,globals,domain,locals⟩ := sszCheckOffsets_call_returned state
    payloadOffsetCheckArguments offsets 4 540 length args code (by decide) post run
  obtain ⟨_,all,first⟩ := contract
  obtain ⟨readable,equal⟩ := first (by decide)
  exact ⟨readable,equal,all,memory,globals,domain,locals⟩

#print axioms payload_offset_check_returned
end InitECandidate.Runtime
