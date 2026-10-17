import InitECandidate.Runtime.KeccakAbsorbBodyBound
import InitECandidate.Runtime.OriginalKeccakAbsorbCode
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual absorption calls cost at most nineteen ticks, covering both block
alignments, memory errors, and every external permutation outcome. -/
theorem evaluate_keccakAbsorb_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (stateArgument blockArgument : ExpHOL 64) (pointer block : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [stateArgument,blockArgument] = some [.val (.word pointer),.val (.word block)])
    (ticks : 19 ≤ state.clock) :
    let output := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak_absorb_block") [stateArgument,blockArgument]);
    state.clock ≤ output.2.clock + 19 ∧ output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "stp",.val (.word pointer))).update (ofString "blk",.val (.word block))
  let entry := callEntryStateHOLFinite state callee
  have localState : entry.locals.lookup (ofString "stp") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "blk" ≠ ofString "stp" from by decide]
  obtain ⟨result,post,body,cost,remaining,noTimeout⟩ := evaluate_keccakAbsorb_body_bounded entry pointer localState code
    (by change 18 ≤ state.clock - 1; omega)
  have postCost : state.clock ≤ post.clock + 19 := by
    change state.clock - 1 ≤ post.clock + 18 at cost
    omega
  have postRemaining : post.clock ≤ state.clock := by
    change post.clock ≤ state.clock - 1 at remaining
    omega
  have installed : state.code.lookup (ofString "keccak_absorb_block") =
      some ([(ofString "stp",.one),(ofString "blk",.one)],sourceFunctionBody Guest.guestFn_keccak_absorb_block,.one) := by
    rw [code]
    exact originalRuntimeCode_keccakAbsorb_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "keccak_absorb_block") (ofString "stp") (ofString "blk")
    (sourceFunctionBody Guest.guestFn_keccak_absorb_block) pointer block (by decide) installed
  have nonzero : state.clock ≠ 0 := by omega
  simp only [evaluateHOLFiniteState_call,args]
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,body]
  cases result with
  | none => exact ⟨postCost,postRemaining,by simp⟩
  | some result =>
    cases result <;> simp_all [emptyLocalsHOLFinite]
    split <;> simp_all

#print axioms evaluate_keccakAbsorb_call_bounded
end InitECandidate.Runtime
