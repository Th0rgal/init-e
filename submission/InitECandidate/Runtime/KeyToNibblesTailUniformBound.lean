import InitECandidate.Runtime.KeyToNibblesStepFrame
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def KeyToNibblesTailBoundInvariant {F : Type} (state : PanSemStateFiniteExact 64 F) (length : BitVec 64) : Prop :=
  (∃ index : BitVec 64, state.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat) ∧
  state.locals.lookup (ofString "n") = some (.val (.word length))

def keyToNibblesTailBoundRank {F : Type} (state : PanSemStateFiniteExact 64 F) (length : BitVec 64) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => length.toNat - index.toNat
  | _ => 0

/-- The original single-byte tail loop is input-linear without any memory-success assumption. -/
theorem evaluate_keyToNibbles_tail_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F) (length start : BitVec 64)
    (startBound : start.toNat ≤ length.toNat)
    (small : length.toNat + 4 < 2^64)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word start)))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (ticks : length.toNat - start.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state keyToNibblesTailLoop = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat - start.toNat) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → KeyToNibblesTailBoundInvariant post length ∧ keyToNibblesTailBoundRank post length = 0) ∧
      (∀ output, result ≠ some (.returned output)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => KeyToNibblesTailBoundInvariant current length
  have guard : ∀ current : PanSemStateFiniteExact 64 F, invariant current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) =
        some (.val (.word (if keyToNibblesTailBoundRank current length = 0 then 0 else 1))) := by
    rintro current ⟨⟨index,localIndex,bounded⟩,localN⟩
    have rankEq : keyToNibblesTailBoundRank current length = length.toNat - index.toNat := by simp [keyToNibblesTailBoundRank,localIndex]
    have nextNat : (index + 1).toNat = index.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]
      rfl
    by_cases done : keyToNibblesTailBoundRank current length = 0
    · have equal : index = length := by apply BitVec.eq_of_toNat_eq; rw [rankEq] at done; omega
      simp [evalHOLFinite,evalHOLExact,localIndex,localN,Compiler.Encoders.Asm.wordCmpHOL,done,equal]
    · have inside : index < length := by apply BitVec.lt_def.mpr; rw [rankEq] at done; omega
      simp [evalHOLFinite,evalHOLExact,localIndex,localN,Compiler.Encoders.Asm.wordCmpHOL,done,inside]
  have enter : ∀ current : PanSemStateFiniteExact 64 F, invariant current → invariant (decClockHOLFinite current) := by
    intro current valid
    exact valid
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F, keyToNibblesTailBoundRank (decClockHOLFinite current) length = keyToNibblesTailBoundRank current length := by
    intro current
    rfl
  have step : ∀ current : PanSemStateFiniteExact 64 F, invariant current → 0 < keyToNibblesTailBoundRank current length → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current keyToNibblesTailStep = (none,post) ∧ invariant post ∧ keyToNibblesTailBoundRank post length < keyToNibblesTailBoundRank current length) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ output, result ≠ .returned output) ∧
           evaluateHOLFiniteState current keyToNibblesTailStep = (some result,post))) := by
    rintro current ⟨⟨index,localIndex,bounded⟩,localN⟩ positive _
    have rankEq : keyToNibblesTailBoundRank current length = length.toNat - index.toNat := by simp [keyToNibblesTailBoundRank,localIndex]
    have inside : index.toNat + 1 ≤ length.toNat := by rw [rankEq] at positive; omega
    have nextNat : (index + 1).toNat = index.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2 ^ 64; omega)]
      rfl
    obtain ⟨result,post,run,clock,locals,outcome⟩ := evaluate_keyToNibbles_tail_step_frame current index localIndex
    refine ⟨post,by omega,by omega,?_⟩
    rcases outcome with normal | failed
    · obtain ⟨rfl,nextLocal⟩ := normal
      have postValid : KeyToNibblesTailBoundInvariant post length := ⟨⟨index + 1,nextLocal,by rw [nextNat]; omega⟩,(locals (ofString "n") (by decide)).trans localN⟩
      have rankPost : keyToNibblesTailBoundRank post length = length.toNat - (index + 1).toNat := by simp [keyToNibblesTailBoundRank,nextLocal]
      exact Or.inl ⟨run,postValid,by rw [rankPost,rankEq,nextNat]; omega⟩
    · subst result
      exact Or.inr ⟨.error,by simp,by simp,by simp,(by intro output; simp),run⟩
  have initialRank : keyToNibblesTailBoundRank state length = length.toNat - start.toNat := by simp [keyToNibblesTailBoundRank,initial]
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) keyToNibblesTailStep invariant (fun current => keyToNibblesTailBoundRank current length) 0 guard enter sameRank step
    state ⟨⟨start,initial,startBound⟩,nLocal⟩ (by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using ticks)
  rw [source_keyToNibbles_tail_loop]
  exact ⟨result,post,run,by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using cost,remaining,noTimeout,completed,noReturn⟩

#print axioms evaluate_keyToNibbles_tail_loop_bounded
end InitECandidate.Runtime
