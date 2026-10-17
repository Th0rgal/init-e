import InitECandidate.Runtime.LoadOneWord
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A successful one-word load exposes its actual pointer, domain membership
and memory word. -/
theorem eval_load_one_read {F : Type} (state : PanSemStateFiniteExact 64 F)
    (address : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.load .one address) = some value) :
    ∃ pointer word : BitVec 64,
      @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address)) address = some (.val (.word pointer)) ∧
      state.memaddrs pointer ∧ state.memory pointer = .word word ∧ value = .val (.word word) := by
  rw [evalHOLExact] at evaluated
  simp only [isWfShapeExactHOL,if_true] at evaluated
  split at evaluated
  · rename_i pointer loaded
    rw [memLoadHOLExact] at evaluated
    split at evaluated
    · rename_i accessible
      cases memory : state.memory pointer with
      | word word =>
        rw [memory] at evaluated
        exact ⟨pointer,word,loaded,accessible,memory,(Option.some.inj evaluated).symm⟩
    · cases evaluated
  · cases evaluated

#print axioms eval_load_one_read
end InitECandidate.Runtime
