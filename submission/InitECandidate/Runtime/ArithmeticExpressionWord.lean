import InitECandidate.Runtime.WordStoreMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem eval_binop_returns_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (operator : BinOp) (arguments : List (ExpHOL 64)) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.op operator arguments) = some value) : ∃ word : BitVec 64, value = .val (.word word) := by
  rw [evalHOLExact] at evaluated
  split at evaluated
  · split at evaluated
    · obtain ⟨word,_,equal⟩ := Option.map_eq_some_iff.mp evaluated
      exact ⟨word,equal.symm⟩
    · cases evaluated
  · cases evaluated

theorem eval_shift_returns_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (operator : Shift) (left right : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.shift operator left right) = some value) : ∃ word : BitVec 64, value = .val (.word word) := by
  rw [evalHOLExact] at evaluated
  split at evaluated
  · obtain ⟨word,_,equal⟩ := Option.map_eq_some_iff.mp evaluated
    exact ⟨word,equal.symm⟩
  · cases evaluated

#print axioms eval_binop_returns_word
#print axioms eval_shift_returns_word
end InitECandidate.Runtime
