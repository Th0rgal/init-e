import InitECandidate.Runtime.StoreAdvance8Step
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def storeAdvance8Condition : ExpHOL 64 :=
  .cmp .less (.var .local (ofString "i")) (.const 136)

def storeAdvance8Rank {F : Type} (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => 17 - index.toNat / 8
  | _ => 0

def StoreAdvance8Invariant {F : Type} (state : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ index : BitVec 64, state.locals.lookup (ofString "i") = some (.val (.word index)) ∧
    index.toNat ≤ 136 ∧ index.toNat % 8 = 0

/-- The absorption loop's store expressions can fail on arbitrary memory.
Every completed iteration advances by eight; at most seventeen ticks are used. -/
theorem evaluate_store_advance8_loop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (ticks : 17 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (.while storeAdvance8Condition (storeAdvance8Body destination value)) = (result,post) ∧
      state.clock ≤ post.clock + 17 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → StoreAdvance8Invariant post ∧ storeAdvance8Rank post = 0) ∧
      (∀ output, result ≠ some (.returned output)) := by
  have guard : ∀ current : PanSemStateFiniteExact 64 F, StoreAdvance8Invariant current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) storeAdvance8Condition =
        some (.val (.word (if storeAdvance8Rank current = 0 then 0 else 1))) := by
    rintro current ⟨index,localIndex,bounded,aligned⟩
    have rankEq : storeAdvance8Rank current = 17 - index.toNat / 8 := by simp [storeAdvance8Rank,localIndex]
    have sign : index.toNat < 2 ^ (64 - 1) := by omega
    by_cases done : index.toNat = 136
    · have zero : storeAdvance8Rank current = 0 := by rw [rankEq,done]
      simp [storeAdvance8Condition,evalHOLFinite,evalHOLExact,localIndex,Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess,sign,done,zero]
    · have inside : index.toNat < 136 := by omega
      have positive : storeAdvance8Rank current ≠ 0 := by rw [rankEq]; omega
      simp [storeAdvance8Condition,evalHOLFinite,evalHOLExact,localIndex,Compiler.Encoders.Asm.wordCmpHOL,Compiler.Encoders.Asm.holAsmSignedLess,sign,inside,positive]
  have enter : ∀ current : PanSemStateFiniteExact 64 F, StoreAdvance8Invariant current → StoreAdvance8Invariant (decClockHOLFinite current) := by
    intro current valid
    exact valid
  have sameRank : ∀ current : PanSemStateFiniteExact 64 F, storeAdvance8Rank (decClockHOLFinite current) = storeAdvance8Rank current := by
    intro current
    rfl
  have step : ∀ current : PanSemStateFiniteExact 64 F, StoreAdvance8Invariant current → 0 < storeAdvance8Rank current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current (storeAdvance8Body destination value) = (none,post) ∧ StoreAdvance8Invariant post ∧ storeAdvance8Rank post < storeAdvance8Rank current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ output, result ≠ .returned output) ∧
           evaluateHOLFiniteState current (storeAdvance8Body destination value) = (some result,post))) := by
    rintro current ⟨index,localIndex,bounded,aligned⟩ positive _
    have rankEq : storeAdvance8Rank current = 17 - index.toNat / 8 := by simp [storeAdvance8Rank,localIndex]
    have inside : index.toNat < 136 := by rw [rankEq] at positive; omega
    have nextNat : (index + 8).toNat = index.toNat + 8 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 8 < 2 ^ 64; omega)]
      rfl
    obtain ⟨result,post,run,clock,outcome⟩ := evaluate_store_advance8_step current destination value index localIndex
    refine ⟨post,by omega,by omega,?_⟩
    rcases outcome with normal | failed
    · obtain ⟨rfl,nextLocal⟩ := normal
      have postValid : StoreAdvance8Invariant post := ⟨index + 8,nextLocal,by rw [nextNat]; omega,by rw [nextNat]; omega⟩
      have rankPost : storeAdvance8Rank post = 17 - (index + 8).toNat / 8 := by simp [storeAdvance8Rank,nextLocal]
      exact Or.inl ⟨run,postValid,by rw [rankPost,rankEq,nextNat]; omega⟩
    · subst result
      exact Or.inr ⟨.error,by simp,by simp,by simp,(by intro output; simp),run⟩
  have initialRank : storeAdvance8Rank state = 17 := by simp [storeAdvance8Rank,initial]
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    storeAdvance8Condition (storeAdvance8Body destination value) StoreAdvance8Invariant storeAdvance8Rank 0 guard enter sameRank step
    state ⟨0,initial,by decide,by decide⟩ (by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using ticks)
  exact ⟨result,post,run,by simpa only [initialRank,Nat.zero_add,Nat.mul_one] using cost,remaining,noTimeout,completed,noReturn⟩

#print axioms evaluate_store_advance8_loop
end InitECandidate.Runtime
