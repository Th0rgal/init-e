import InitECandidate.Runtime.StatelessWitnessSetupSource
import InitECandidate.Runtime.StatelessPrefixStages
import InitECandidate.Runtime.SszSplitVarListStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Loop exit at i = 3. -/
theorem wsLoop_exit {σ : Type} (t : PanSemStateFiniteExact 64 σ)
    (hi : t.locals.lookup (ofString "i") = some (.val (.word 3))) :
    evaluateHOLFiniteState t wsLoop = (none, t) := by
  unfold wsLoop
  rw [evaluateHOLFiniteState_while_total]
  simp [sszLocal, evalHOLFinite, evalHOLExact, hi, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess]

/-- One actual iteration at i = k < 3: abort within one tick, or the exact
scratch store at offsets+8k of a 32-bit value followed by i := k+1. -/
theorem wsLoop_iter {σ : Type} (t : PanSemStateFiniteExact 64 σ) (k offsets : BitVec 64) (hk : k.toNat < 3)
    (hi : t.locals.lookup (ofString "i") = some (.val (.word k)))
    (hg : t.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets))) :
    StAbort t (evaluateHOLFiniteState t wsLoop) 1 ∨
    (t.clock ≠ 0 ∧ ∃ x : BitVec 64, x.toNat < 2 ^ 32 ∧ t.memaddrs (offsets + k * 8) ∧
      evaluateHOLFiniteState t wsLoop = evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word (k + 1)))
        ({decClockHOLFinite t with memory := wmem t.memory (offsets + k * 8) x} : PanSemStateFiniteExact 64 σ)) wsLoop) := by
  have guard : evalHOLFinite t (h := fun address => Classical.propDecidable (t.memaddrs address))
      (.cmp .less (sszLocal "i") (.const 3)) = some (.val (.word 1)) := by
    simp [sszLocal, evalHOLFinite, evalHOLExact, hi, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      Flapjack.Compiler.Encoders.Asm.holAsmSignedLess]
    omega
  unfold wsLoop
  rw [evaluateHOLFiniteState_while_total, guard]
  simp only [ne_eq, (by decide : ¬ (1 : BitVec 64) = 0), not_false_eq_true, if_true]
  by_cases zero : t.clock = 0
  · rw [if_pos zero]
    exact Or.inl ⟨.timeOut, rfl, by simp, by simp [emptyLocalsHOLFinite], by simp [emptyLocalsHOLFinite], by omega⟩
  · rw [if_neg zero]
    try dsimp only
    rw [fixClockHOLFinite_evaluateState]
    generalize he : decClockHOLFinite t = entry
    have ei : entry.locals.lookup (ofString "i") = some (.val (.word k)) := by rw [← he]; exact hi
    have eg : entry.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by rw [← he]; exact hg
    have ec : entry.clock = t.clock - 1 := by rw [← he]; rfl
    have ed : entry.memaddrs = t.memaddrs := by rw [← he]; rfl
    have addr : @evalHOLExact 64 σ _ entry.toExact (fun a => Classical.propDecidable (entry.memaddrs a))
        (.op .add [stOffsetsGlobal, .panop .mul [sszLocal "i", .const 8]]) = some (.val (.word (offsets + k * 8))) := by
      simp [stOffsetsGlobal, sszLocal, evalHOLExact, evalListHOLExact, ei, eg, wordOpHOL, wordOp, valueIsWord,
        valueWord, panOpHOL]
    unfold wsBody
    rw [evaluateHOLFiniteState_seq_line780]
    have errorCase : StAbort t (some .error, entry) 1 :=
      ⟨.error, rfl, by simp, by simp; omega, by simp; omega, fun _ => by simp⟩
    cases hv : @evalHOLExact 64 σ _ entry.toExact (fun x => Classical.propDecidable (entry.memaddrs x)) wsRead with
    | none =>
      left
      rw [evaluateHOLFiniteState_store, addr]
      simp only [hv]
      exact errorCase
    | some v =>
      obtain ⟨x, rfl, small⟩ := @wsRead_bounded σ entry.toExact (fun x => Classical.propDecidable (entry.memaddrs x)) _ hv
      by_cases dom : entry.memaddrs (offsets + k * 8)
      · rw [sszStore_in entry _ x _ _ addr hv dom]
        try dsimp only
        rw [sszSplit_assign_i ({entry with memory := wmem entry.memory (offsets + k * 8) x} : PanSemStateFiniteExact 64 σ)
          k ei]
        try dsimp only
        right
        refine ⟨zero, x, small, by rw [← ed]; exact dom, ?_⟩
        rw [← he]; rfl
      · rw [sszStore_out entry _ x _ _ addr hv dom]
        left
        exact errorCase

#print axioms wsLoop_iter
end InitECandidate.Runtime
