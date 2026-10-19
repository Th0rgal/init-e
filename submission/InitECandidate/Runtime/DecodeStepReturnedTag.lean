import InitECandidate.Runtime.ReachesReturnedContinuation
import InitECandidate.Runtime.ReturnedPairTagSyntax
import InitECandidate.Runtime.DecodeStepEntryParseReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The complete dispatch after parsing contains only the actual completed-node
and stack-push return tags, including every two-item and branch constructor. -/
theorem decode_step_dispatch_returned_tag {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (decodeStepAt 3) = (some (.returned value),post)) :
    ∃ tag payload, (tag = (0 : BitVec 64) ∨ tag = 1) ∧
      value = .rStruct [.val (.word tag),payload] := by
  have certified : returnedPairTagSyntax [0,1] (decodeStepAt 3) = true := by
    unfold decodeStepAt sourceFunctionBody
    rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  obtain ⟨tag,payload,member,same⟩ := evaluate_returnedPairTagSyntax [0,1] (decodeStepAt 3) certified s post value run
  exact ⟨tag,payload,by simpa using member,same⟩

theorem source_decode_step_entry : sourceFunctionBody Guest.guestFn__decode_step = decodeStepAt 0 := rfl

/-- Every returned result of the original decoder has one of its two control
flags. The real entry parse is included; invalid input may reject earlier. -/
theorem decode_step_entry_returned_tag {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (Flapjack.Basis.Pure.MlString.ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (Flapjack.Basis.Pure.MlString.ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepParseCost length.toNat ≤ s.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_step) = (some (.returned value),post)) :
    ∃ tag payload, (tag = (0 : BitVec 64) ∨ tag = 1) ∧
      value = .rStruct [.val (.word tag),payload] := by
  rw [source_decode_step_entry] at run
  have reached := decode_step_entry_parse_reaches s pointer length scratch frame ceiling inputLimit atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  obtain ⟨ready,_,_,_,_,returned⟩ := reaches_returned_continuation s (decodeStepAt 0) (decodeStepAt 3)
    _ _ _ reached (by rw [run])
  cases tailRun : evaluateHOLFiniteState ready (decodeStepAt 3) with
  | mk result output =>
    rw [tailRun] at returned
    dsimp only at returned
    subst result
    exact decode_step_dispatch_returned_tag ready output value tailRun

#print axioms decode_step_entry_returned_tag
#print axioms decode_step_dispatch_returned_tag
end InitECandidate.Runtime
