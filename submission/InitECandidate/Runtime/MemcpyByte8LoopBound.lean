import InitECandidate.Runtime.MemcpyByte8Progress
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memcpyByte8Rank {F : Type} (size : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => (size.toNat - index.toNat) / 8
  | _ => 0

/-- The real unaligned copy loop consumes at most one clock per eight-byte
block, including arbitrary load/store failures. -/
theorem evaluate_memcpy_byte8_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index size : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (budget : (size.toNat - index.toNat) / 8 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memcpyByte8Loop = (result,post) ∧
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
      memcpyByte8Rank size current = (size.toNat - i.toNat) / 8 := by
    intro current i binding; simp [memcpyByte8Rank,binding]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a)) (memzeroBlockCondition 8) =
      some (.val (.word (if memcpyByte8Rank size current = 0 then 0 else 1))) := by
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
      memcpyByte8Rank size (decClockHOLFinite current) = memcpyByte8Rank size current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < memcpyByte8Rank size current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current memcpyByte8Body = (none,post) ∧ invariant post ∧
          memcpyByte8Rank size post < memcpyByte8Rank size current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current memcpyByte8Body = (some result,post))) := by
    rintro current ⟨i,atIndex,atSize,bounded⟩ positive _
    obtain ⟨result,post,run,clock,locals,normal⟩ := evaluate_memcpy_byte8_progress current i atIndex
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
    (memzeroBlockCondition 8) memcpyByte8Body invariant (memcpyByte8Rank size) 0 guard enter entryRank step state
    ⟨index,indexLocal,sizeLocal,inside⟩ (by simpa [rankEq state index indexLocal] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · rw [memcpyByte8Loop_shape]; exact run
  · simpa [rankEq state index indexLocal] using cost
  · intro normal
    obtain ⟨⟨i,atIndex,atSize,bounded⟩,zero⟩ := done normal
    rw [rankEq post i atIndex] at zero
    exact ⟨i,atIndex,atSize,bounded,by omega⟩

#print axioms evaluate_memcpy_byte8_loop_bounded
end InitECandidate.Runtime
