import InitECandidate.Runtime.OutputWriteLoopBound
import InitECandidate.Runtime.SszSplitVarListFirstStage
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete output writer body consumes at most one source clock per
requested byte, including malformed source pointers and early host exit. -/
theorem evaluate_outputWrite_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (size : BitVec 64) (atSize : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (budget : size.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_output_write)
    state.clock ≤ evaluated.2.clock + size.toNat ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_outputWrite_body]
  apply evaluate_dec_word_post state (ofString "i") (.const 0) _ (0 : BitVec 64) size.toNat
    (fun r _ => r ≠ some .timeOut) (fun _ _ _ h => h) (by simp [evalHOLExact])
  let entry := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have zero : entry.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atSize,
      show ofString "i" ≠ ofString "n" by decide]
  obtain ⟨result,post,run,spent,kept,safe,_,_⟩ := evaluate_outputWrite_loop_bounded entry 0 size zero n
    (by simp) (by simpa [entry,setVarHOLFinite] using budget)
  have loopBound : entry.clock ≤ (evaluateHOLFiniteState entry outputWriteLoop).2.clock + size.toNat ∧
      (evaluateHOLFiniteState entry outputWriteLoop).2.clock ≤ entry.clock ∧
      (evaluateHOLFiniteState entry outputWriteLoop).1 ≠ some .timeOut := by
    rw [run]
    simpa using And.intro spent (And.intro kept safe)
  exact evaluate_sequence_straight_bounded entry outputWriteLoop (.return (.const 0)) size.toNat loopBound (by rfl)

#print axioms evaluate_outputWrite_body_bounded
end InitECandidate.Runtime
