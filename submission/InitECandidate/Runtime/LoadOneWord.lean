import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Successful one-word loads in this exact evaluator produce integer words.
No address-domain or loaded-value witness needs to be assumed separately. -/
theorem eval_load_one_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (address : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.load .one address) = some value) :
    ∃ word : BitVec 64, value = .val (.word word) := by
  rw [evalHOLExact] at evaluated
  simp only [isWfShapeExactHOL,if_true] at evaluated
  split at evaluated
  · rename_i pointer loaded
    rw [memLoadHOLExact] at evaluated
    split at evaluated
    · cases memory : state.memory pointer with
      | word word =>
        rw [memory] at evaluated
        exact ⟨word,(Option.some.inj evaluated).symm⟩
    · cases evaluated
  · cases evaluated

#print axioms eval_load_one_word
end InitECandidate.Runtime
