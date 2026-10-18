import InitECandidate.Runtime.StatelessWitnessCheckBound
import InitECandidate.Runtime.StatelessWitnessSetupRun
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original witness decoder, starting at its length guard,
uses at most witnessLength+23 clocks. Malformed input, offset rejection,
heap exhaustion and failed stores are all included. -/
theorem evaluate_stateless_witness_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "wp") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "wlen") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : length.toNat + 23 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (statelessAt 32)
    state.clock ≤ evaluated.2.clock + (length.toNat + 23) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rcases evaluate_stateless_witness_setup state length offsets code atLength atOffsets with
    ⟨entry,w0,w1,w2,valid,source⟩ | aborted
  · obtain ⟨_,_,locals,globals,domain,installed,positive,clock,_⟩ := valid
    have tail := evaluate_stateless_witness_check_bounded entry pointer length offsets heapPointer
      ((locals _ (by decide)).trans atPointer) ((locals _ (by decide)).trans atLength)
      (by rw [globals]; exact atOffsets) (by rw [globals]; exact heap) heapBound
      (installed.trans code) (by rw [clock]; omega)
    rw [source]
    cases run : evaluateHOLFiniteState entry (statelessAt 35) with
    | mk result output =>
      rw [run] at tail
      dsimp only at tail ⊢
      exact ⟨by have consumed := tail.1; omega,by have remaining := tail.2.1; omega,tail.2.2⟩
  · obtain ⟨result,ran,_,consumed,remaining,nt⟩ := aborted
    refine ⟨by omega,remaining,?_⟩
    intro timedOut
    exact nt (by omega) (Option.some.inj (ran.symm.trans timedOut))

#print axioms evaluate_stateless_witness_body_bounded
end InitECandidate.Runtime
