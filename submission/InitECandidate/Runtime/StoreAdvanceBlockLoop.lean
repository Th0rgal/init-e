import InitECandidate.Runtime.StoreAdvanceStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def storeBlock32Rank {F : Type} (size : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => (size.toNat - index.toNat) / 32
  | _ => 0

/-- Any store-and-advance loop guarded by i+32 <= n consumes at most one
clock per 32-byte block, including arbitrary store failures. -/
theorem evaluate_storeAdvance_block32_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64) (body : ProgHOL 64)
    (supported : StoreAdvanceStep (ofString "i") 32 body)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) / 32 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (.while (memzeroBlockCondition 32) body) = (result,post) ∧
      state.clock ≤ post.clock + (size.toNat - index.toNat) / 32 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ finalIndex : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word size)) ∧
        finalIndex.toNat ≤ size.toNat ∧ size.toNat - finalIndex.toNat < 32) ∧
      (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => ∃ i : BitVec 64,
    current.locals.lookup (ofString "i") = some (.val (.word i)) ∧
    current.locals.lookup (ofString "n") = some (.val (.word size)) ∧ i.toNat ≤ size.toNat
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ i : BitVec 64,
      current.locals.lookup (ofString "i") = some (.val (.word i)) →
      storeBlock32Rank size current = (size.toNat - i.toNat) / 32 := by
    intro current i binding; simp [storeBlock32Rank,binding]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a)) (memzeroBlockCondition 32) =
      some (.val (.word (if storeBlock32Rank size current = 0 then 0 else 1))) := by
    rintro current ⟨i,atIndex,atSize,bounded⟩
    have natural : (i + 32).toNat = i.toNat + 32 := by
      rw [BitVec.toNat_add_of_lt (by change i.toNat + 32 < 2^64; omega)]; rfl
    rw [evalHOLFinite_eq_toExact,eval_memzero_block_condition current i size 32 atIndex atSize,rankEq current i atIndex]
    by_cases enabled : i.toNat + 32 ≤ size.toNat
    · have nonzero : (size.toNat - i.toNat) / 32 ≠ 0 := by omega
      have flag : Compiler.Encoders.Asm.wordCmpHOL .notLower size (i + 32) = true := by
        change (!decide (size.toNat < (i + 32).toNat)) = true
        rw [natural]; simp; omega
      simp [nonzero]
      exact flag
    · have zero : (size.toNat - i.toNat) / 32 = 0 := by omega
      have flag : Compiler.Encoders.Asm.wordCmpHOL .notLower size (i + 32) = false := by
        change (!decide (size.toNat < (i + 32).toNat)) = false
        rw [natural]; simp; omega
      simp [zero]
      exact flag
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨i,atIndex,atSize,bounded⟩; exact ⟨i,atIndex,atSize,bounded⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      storeBlock32Rank size (decClockHOLFinite current) = storeBlock32Rank size current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < storeBlock32Rank size current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current body = (none,post) ∧ invariant post ∧
          storeBlock32Rank size post < storeBlock32Rank size current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current body = (some result,post))) := by
    rintro current ⟨i,atIndex,atSize,bounded⟩ positive _
    obtain ⟨result,post,run,clock,locals,normal⟩ := evaluate_storeAdvanceStep supported current i atIndex
    refine ⟨post,by omega,by omega,?_⟩
    rcases normal with ⟨rfl,advanced⟩ | rfl
    · have natural : (i + 32).toNat = i.toNat + 32 := by
        rw [BitVec.toNat_add_of_lt (by change i.toNat + 32 < 2^64; omega)]; rfl
      rw [rankEq current i atIndex] at positive
      refine Or.inl ⟨run,⟨i+32,advanced,(locals _ (by decide)).trans atSize,by omega⟩,?_⟩
      rw [rankEq post (i+32) advanced,rankEq current i atIndex,natural]
      omega
    · exact Or.inr ⟨.error,by simp,by simp,by simp,(by intro value; simp),run⟩
  obtain ⟨result,post,run,cost,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (memzeroBlockCondition 32) body invariant (storeBlock32Rank size) 0 guard enter entryRank step state
    ⟨index,indexLocal,sizeLocal,inside⟩ (by simpa [rankEq state index indexLocal] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · exact run
  · simpa [rankEq state index indexLocal] using cost
  · intro normal
    obtain ⟨⟨i,atIndex,atSize,bounded⟩,zero⟩ := done normal
    rw [rankEq post i atIndex] at zero
    exact ⟨i,atIndex,atSize,bounded,by omega⟩

#print axioms evaluate_storeAdvance_block32_loop_bounded

def storeBlock8Rank {F : Type} (size : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => (size.toNat - index.toNat) / 8
  | _ => 0

/-- Any store-and-advance loop guarded by i+8 <= n consumes at most one
clock per 8-byte block, including arbitrary store failures. -/
theorem evaluate_storeAdvance_block8_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64) (body : ProgHOL 64)
    (supported : StoreAdvanceStep (ofString "i") 8 body)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) / 8 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (.while (memzeroBlockCondition 8) body) = (result,post) ∧
      state.clock ≤ post.clock + (size.toNat - index.toNat) / 8 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ finalIndex : BitVec 64,
        post.locals.lookup (ofString "i") = some (.val (.word finalIndex)) ∧
        post.locals.lookup (ofString "n") = some (.val (.word size)) ∧
        finalIndex.toNat ≤ size.toNat ∧ size.toNat - finalIndex.toNat < 8) ∧
      (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => ∃ i : BitVec 64,
    current.locals.lookup (ofString "i") = some (.val (.word i)) ∧
    current.locals.lookup (ofString "n") = some (.val (.word size)) ∧ i.toNat ≤ size.toNat
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ i : BitVec 64,
      current.locals.lookup (ofString "i") = some (.val (.word i)) →
      storeBlock8Rank size current = (size.toNat - i.toNat) / 8 := by
    intro current i binding; simp [storeBlock8Rank,binding]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a)) (memzeroBlockCondition 8) =
      some (.val (.word (if storeBlock8Rank size current = 0 then 0 else 1))) := by
    rintro current ⟨i,atIndex,atSize,bounded⟩
    have natural : (i + 8).toNat = i.toNat + 8 := by
      rw [BitVec.toNat_add_of_lt (by change i.toNat + 8 < 2^64; omega)]; rfl
    rw [evalHOLFinite_eq_toExact,eval_memzero_block_condition current i size 8 atIndex atSize,rankEq current i atIndex]
    by_cases enabled : i.toNat + 8 ≤ size.toNat
    · have nonzero : (size.toNat - i.toNat) / 8 ≠ 0 := by omega
      have flag : Compiler.Encoders.Asm.wordCmpHOL .notLower size (i + 8) = true := by
        change (!decide (size.toNat < (i + 8).toNat)) = true
        rw [natural]; simp; omega
      simp [nonzero]
      exact flag
    · have zero : (size.toNat - i.toNat) / 8 = 0 := by omega
      have flag : Compiler.Encoders.Asm.wordCmpHOL .notLower size (i + 8) = false := by
        change (!decide (size.toNat < (i + 8).toNat)) = false
        rw [natural]; simp; omega
      simp [zero]
      exact flag
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨i,atIndex,atSize,bounded⟩; exact ⟨i,atIndex,atSize,bounded⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      storeBlock8Rank size (decClockHOLFinite current) = storeBlock8Rank size current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < storeBlock8Rank size current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current body = (none,post) ∧ invariant post ∧
          storeBlock8Rank size post < storeBlock8Rank size current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current body = (some result,post))) := by
    rintro current ⟨i,atIndex,atSize,bounded⟩ positive _
    obtain ⟨result,post,run,clock,locals,normal⟩ := evaluate_storeAdvanceStep supported current i atIndex
    refine ⟨post,by omega,by omega,?_⟩
    rcases normal with ⟨rfl,advanced⟩ | rfl
    · have natural : (i + 8).toNat = i.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt (by change i.toNat + 8 < 2^64; omega)]; rfl
      rw [rankEq current i atIndex] at positive
      refine Or.inl ⟨run,⟨i+8,advanced,(locals _ (by decide)).trans atSize,by omega⟩,?_⟩
      rw [rankEq post (i+8) advanced,rankEq current i atIndex,natural]
      omega
    · exact Or.inr ⟨.error,by simp,by simp,by simp,(by intro value; simp),run⟩
  obtain ⟨result,post,run,cost,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (memzeroBlockCondition 8) body invariant (storeBlock8Rank size) 0 guard enter entryRank step state
    ⟨index,indexLocal,sizeLocal,inside⟩ (by simpa [rankEq state index indexLocal] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · exact run
  · simpa [rankEq state index indexLocal] using cost
  · intro normal
    obtain ⟨⟨i,atIndex,atSize,bounded⟩,zero⟩ := done normal
    rw [rankEq post i atIndex] at zero
    exact ⟨i,atIndex,atSize,bounded,by omega⟩

#print axioms evaluate_storeAdvance_block8_loop_bounded

end InitECandidate.Runtime
