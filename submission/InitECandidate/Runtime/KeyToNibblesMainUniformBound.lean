import InitECandidate.Runtime.KeyToNibblesStepFrame
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def KeyToNibblesBoundInvariant {F : Type} (state : PanSemStateFiniteExact 64 F) (length : BitVec 64) : Prop :=
  (∃ index : BitVec 64, state.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat ∧ index.toNat % 4 = 0) ∧
  state.locals.lookup (ofString "n") = some (.val (.word length))

def keyToNibblesBoundRank {F : Type} (state : PanSemStateFiniteExact 64 F) (length : BitVec 64) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => length.toNat / 4 - index.toNat / 4
  | _ => 0

/-- The original full-block loop is input-linear without any memory-success assumption. -/
theorem evaluate_keyToNibbles_main_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F) (length : BitVec 64)
    (small : length.toNat + 4 < 2^64)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (ticks : length.toNat / 4 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state keyToNibblesMainLoop = (result,post) ∧
      state.clock ≤ post.clock + length.toNat / 4 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → KeyToNibblesBoundInvariant post length ∧ keyToNibblesBoundRank post length = 0) ∧
      (∀ output, result ≠ some (.returned output)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => KeyToNibblesBoundInvariant current length
  have guard : ∀ current : PanSemStateFiniteExact 64 F, invariant current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 4])) =
        some (.val (.word (if keyToNibblesBoundRank current length = 0 then 0 else 1))) := by
    rintro current ⟨⟨index,localIndex,bounded,aligned⟩,localN⟩
    have rankEq : keyToNibblesBoundRank current length = length.toNat / 4 - index.toNat / 4 := by simp [keyToNibblesBoundRank,localIndex]
    have nextNat : (index + 4).toNat = index.toNat + 4 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 4 < 2 ^ 64; omega)]
      rfl
    by_cases done : keyToNibblesBoundRank current length = 0
    · have zero : keyToNibblesBoundRank current length = 0 := done
      simp [evalHOLFinite,evalHOLExact,evalListHOLExact,localIndex,localN,wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,zero]
      apply BitVec.lt_def.mpr
      change length.toNat < (index + 4).toNat
      rw [nextNat]
      rw [rankEq] at done
      omega
    · have positive : keyToNibblesBoundRank current length ≠ 0 := done
      have inside : (index + 4) ≤ length := by
        apply BitVec.le_def.mpr
        rw [nextNat]
        change index.toNat + 4 ≤ length.toNat
        rw [rankEq] at positive
        omega
      simp [evalHOLFinite,evalHOLExact,evalListHOLExact,localIndex,localN,wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,positive]
      exact inside
  have enter : ∀ current : PanSemStateFiniteExact 64 F, invariant current → invariant (decClockHOLFinite current) := by
    intro current valid
    exact valid
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F, keyToNibblesBoundRank (decClockHOLFinite current) length = keyToNibblesBoundRank current length := by
    intro current
    rfl
  have step : ∀ current : PanSemStateFiniteExact 64 F, invariant current → 0 < keyToNibblesBoundRank current length → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current keyToNibblesMainStep = (none,post) ∧ invariant post ∧ keyToNibblesBoundRank post length < keyToNibblesBoundRank current length) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ output, result ≠ .returned output) ∧
           evaluateHOLFiniteState current keyToNibblesMainStep = (some result,post))) := by
    rintro current ⟨⟨index,localIndex,bounded,aligned⟩,localN⟩ positive _
    have rankEq : keyToNibblesBoundRank current length = length.toNat / 4 - index.toNat / 4 := by simp [keyToNibblesBoundRank,localIndex]
    have inside : index.toNat + 4 ≤ length.toNat := by rw [rankEq] at positive; omega
    have nextNat : (index + 4).toNat = index.toNat + 4 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 4 < 2 ^ 64; omega)]
      rfl
    obtain ⟨result,post,run,clock,locals,outcome⟩ := evaluate_keyToNibbles_main_step_frame current index localIndex
    refine ⟨post,by omega,by omega,?_⟩
    rcases outcome with normal | failed
    · obtain ⟨rfl,nextLocal⟩ := normal
      have postValid : KeyToNibblesBoundInvariant post length := ⟨⟨index + 4,nextLocal,by rw [nextNat]; omega,by rw [nextNat]; omega⟩,(locals (ofString "n") (by decide)).trans localN⟩
      have rankPost : keyToNibblesBoundRank post length = length.toNat / 4 - (index + 4).toNat / 4 := by simp [keyToNibblesBoundRank,nextLocal]
      exact Or.inl ⟨run,postValid,by rw [rankPost,rankEq,nextNat]; omega⟩
    · subst result
      exact Or.inr ⟨.error,by simp,by simp,by simp,(by intro output; simp),run⟩
  have initialRank : keyToNibblesBoundRank state length = length.toNat / 4 := by simp [keyToNibblesBoundRank,initial]
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 4])) keyToNibblesMainStep invariant (fun current => keyToNibblesBoundRank current length) 0 guard enter sameRank step
    state ⟨⟨0,initial,by simp,by decide⟩,nLocal⟩ (by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using ticks)
  rw [source_keyToNibbles_main_loop]
  exact ⟨result,post,run,by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using cost,remaining,noTimeout,completed,noReturn⟩

#print axioms evaluate_keyToNibbles_main_loop_bounded
end InitECandidate.Runtime
