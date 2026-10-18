import InitECandidate.Runtime.OutputWriteBodyBound
import InitECandidate.Runtime.OriginalOutputWriteCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original output-write call costs at most size+1 source clocks,
including call entry, invalid memory accesses and early host termination. -/
theorem evaluate_outputWrite_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) (pointer size : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word size)])
    (code : state.code = originalRuntimeCode) (budget : size.toNat + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "output_write") arguments)
    state.clock ≤ evaluated.2.clock + (size.toNat + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "src",.val (.word pointer))).update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have n : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_outputWrite_body_bounded entry size n (by change size.toNat ≤ state.clock - 1; omega)
  have lookup := pan_two_word_lookup state.code.lookup (ofString "output_write") (ofString "src") (ofString "n")
    (sourceFunctionBody Guest.guestFn_output_write) pointer size (by decide)
    (by rw [code]; exact originalRuntimeCode_outputWrite_lookup)
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_output_write) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have evaluated := evaluate_call_body_clock_no_timeout state post (ofString "output_write") destination arguments _
      (sourceFunctionBody Guest.guestFn_output_write) callee .one result args lookup (by omega) bodyRun bounded.2.2
    dsimp only
    rw [evaluated.2]
    have spent : state.clock - 1 ≤ post.clock + size.toNat := bounded.1
    have kept : post.clock ≤ state.clock - 1 := bounded.2.1
    exact ⟨by omega,by omega,evaluated.1⟩

#print axioms evaluate_outputWrite_call_bounded
end InitECandidate.Runtime
