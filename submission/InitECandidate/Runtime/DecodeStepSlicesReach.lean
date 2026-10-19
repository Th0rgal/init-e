import InitECandidate.Runtime.DecodeStepKindDispatch
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.RlpSlicesBodyBound
import InitECandidate.Runtime.RlpSlicesBodyRuntimeContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepSlicesCost (n : Nat) : Nat := n * ((2*n+1)*15+19) + n*12+4

theorem source_decode_step_slices : decodeStepAt 4 =
    .decCall (ofString "sl") (.comb [.one,.one]) (ofString "rlp_list_to_slices")
      [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))]
      (decodeStepAt 5) := by
  simp only [decodeStepAt,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual list conversion reaches its continuation with the exact returned
callee run. Keeping that run connects slice contents and heap endpoints to the
same state used by subsequent node construction. -/
theorem decode_step_slices_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length consumed scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepSlicesCost length.toNat ≤ s.clock) :
    Reaches s (decodeStepAt 4)
      (fun next => ∃ value post,
        evaluateHOLFiniteState (callEntryStateHOLFinite s (rlpHeaderCallee pointer length))
          (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),post) ∧
        shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one]) = true ∧
        next = setVarHOLFinite (ofString "sl") value {post with locals := s.locals})
      (decodeStepSlicesCost length.toNat) (decodeStepAt 5) := by
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_rlpSlices_body_bounded entry pointer length scratch frame ceiling inputLimit p n
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change _ ≤ s.clock - 1; unfold decodeStepSlicesCost at budget; omega)
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))] =
      some [.val (.word pointer),.val (.word length)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atItem]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_list_to_slices")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
    (.comb [.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpSlices_lookup)
  rw [source_decode_step_slices]
  exact bounded_decCall_reaches s (ofString "sl") (ofString "rlp_list_to_slices")
    (.comb [.one,.one]) (.comb [.one,.one]) _ _ _ _ (rlpHeaderCallee pointer length)
    (length.toNat*((2*length.toNat+1)*15+19)+length.toNat*12+3) _ args lookup
    (by unfold decodeStepSlicesCost at budget; omega) bounded
    (by intro value post run shapes; exact ⟨value,post,run,shapes.1,rfl⟩)

#print axioms source_decode_step_slices
#print axioms decode_step_slices_reaches
end InitECandidate.Runtime
