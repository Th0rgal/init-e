import InitECandidate.Runtime.KeyToNibblesStepFrame
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def KeyToNibbles32Invariant {F : Type} (state : PanSemStateFiniteExact 64 F) : Prop :=
  (∃ index : BitVec 64, state.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ 32 ∧ index.toNat % 4 = 0) ∧
  state.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64)))

def keyToNibbles32Rank {F : Type} (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => 8 - index.toNat / 4
  | _ => 0

/-- The original full-block loop for a 32-byte trie key needs at most eight
source ticks. Invalid byte accesses exit early, without timeout. -/
theorem evaluate_keyToNibbles32_main_loop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64))))
    (ticks : 8 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state keyToNibblesMainLoop = (result,post) ∧
      state.clock ≤ post.clock + 8 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → KeyToNibbles32Invariant post ∧ keyToNibbles32Rank post = 0) ∧
      (∀ output, result ≠ some (.returned output)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => KeyToNibbles32Invariant current
  have guard : ∀ current : PanSemStateFiniteExact 64 F, invariant current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 4])) =
        some (.val (.word (if keyToNibbles32Rank current = 0 then 0 else 1))) := by
    rintro current ⟨⟨index,localIndex,bounded,aligned⟩,localN⟩
    have rankEq : keyToNibbles32Rank current = 8 - index.toNat / 4 := by simp [keyToNibbles32Rank,localIndex]
    have nextNat : (index + 4).toNat = index.toNat + 4 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 4 < 2 ^ 64; omega)]
      rfl
    by_cases done : index.toNat = 32
    · have zero : keyToNibbles32Rank current = 0 := by rw [rankEq,done]
      simp [evalHOLFinite,evalHOLExact,evalListHOLExact,localIndex,localN,wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,zero]
      apply BitVec.lt_def.mpr
      change 32 < (index + 4).toNat
      rw [nextNat]
      omega
    · have positive : keyToNibbles32Rank current ≠ 0 := by rw [rankEq]; omega
      have inside : (index + 4) ≤ (32 : BitVec 64) := by
        apply BitVec.le_def.mpr
        rw [nextNat]
        change index.toNat + 4 ≤ 32
        omega
      simp [evalHOLFinite,evalHOLExact,evalListHOLExact,localIndex,localN,wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,positive]
      exact inside
  have enter : ∀ current : PanSemStateFiniteExact 64 F, invariant current → invariant (decClockHOLFinite current) := by
    intro current valid
    exact valid
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F, keyToNibbles32Rank (decClockHOLFinite current) = keyToNibbles32Rank current := by
    intro current
    rfl
  have step : ∀ current : PanSemStateFiniteExact 64 F, invariant current → 0 < keyToNibbles32Rank current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current keyToNibblesMainStep = (none,post) ∧ invariant post ∧ keyToNibbles32Rank post < keyToNibbles32Rank current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ output, result ≠ .returned output) ∧
           evaluateHOLFiniteState current keyToNibblesMainStep = (some result,post))) := by
    rintro current ⟨⟨index,localIndex,bounded,aligned⟩,localN⟩ positive _
    have rankEq : keyToNibbles32Rank current = 8 - index.toNat / 4 := by simp [keyToNibbles32Rank,localIndex]
    have inside : index.toNat < 32 := by rw [rankEq] at positive; omega
    have nextNat : (index + 4).toNat = index.toNat + 4 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 4 < 2 ^ 64; omega)]
      rfl
    obtain ⟨result,post,run,clock,locals,outcome⟩ := evaluate_keyToNibbles_main_step_frame current index localIndex
    refine ⟨post,by omega,by omega,?_⟩
    rcases outcome with normal | failed
    · obtain ⟨rfl,nextLocal⟩ := normal
      have postValid : KeyToNibbles32Invariant post := ⟨⟨index + 4,nextLocal,by rw [nextNat]; omega,by rw [nextNat]; omega⟩,(locals (ofString "n") (by decide)).trans localN⟩
      have rankPost : keyToNibbles32Rank post = 8 - (index + 4).toNat / 4 := by simp [keyToNibbles32Rank,nextLocal]
      exact Or.inl ⟨run,postValid,by rw [rankPost,rankEq,nextNat]; omega⟩
    · subst result
      exact Or.inr ⟨.error,by simp,by simp,by simp,(by intro output; simp),run⟩
  have initialRank : keyToNibbles32Rank state = 8 := by simp [keyToNibbles32Rank,initial]
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 4])) keyToNibblesMainStep invariant keyToNibbles32Rank 0 guard enter sameRank step
    state ⟨⟨0,initial,by decide,by decide⟩,nLocal⟩ (by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using ticks)
  rw [source_keyToNibbles_main_loop]
  exact ⟨result,post,run,by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using cost,remaining,noTimeout,completed,noReturn⟩

#print axioms evaluate_keyToNibbles32_main_loop
end InitECandidate.Runtime
