import InitECandidate.Runtime.MemeqWord8Bound
import InitECandidate.Runtime.MemeqByte1BoundCap
import InitECandidate.Runtime.MemeqWordLoopSteps
import InitECandidate.Runtime.RankedLoopReturnsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original eight-byte word comparison loop uses at most n source ticks
for lengths up to the heap cap, including early mismatch returns and invalid memory. -/
theorem evaluate_memeq_word8_bounded_cap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (size index : BitVec 64)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (bounded : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496) (ticks : size.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memeqWord8Loop = (result,post) ∧
      state.clock ≤ post.clock + size.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → MemeqByteInvariant size post ∧ memeqWord8Rank size post = 0) := by
  let invariant := MemeqByteInvariant (F := F) size
  let rank := memeqWord8Rank (F := F) size
  let condition : ExpHOL 64 := .cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 8])
  have guard : ∀ current : PanSemStateFiniteExact 64 F, invariant current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) condition =
        some (.val (.word (if rank current = 0 then 0 else 1))) := by
    rintro current ⟨⟨i,localI,inside⟩,localN⟩
    have rankEq : rank current = (size.toNat - i.toNat) / 8 := by simp [rank,memeqWord8Rank,localI]
    have nextNat : (i + 8).toNat = i.toNat + 8 := by
      rw [BitVec.toNat_add_of_lt (by change i.toNat + 8 < 2 ^ 64; omega)]
      rfl
    by_cases done : rank current = 0
    · have outside : size < i + 8 := by
        apply BitVec.lt_def.mpr
        rw [nextNat]
        rw [rankEq] at done
        omega
      simp [condition,evalHOLFinite,evalHOLExact,evalListHOLExact,localI,localN,wordOpHOL,wordOp,valueIsWord,valueWord,done,Compiler.Encoders.Asm.wordCmpHOL]
      exact outside
    · have below : i + 8 ≤ size := by
        apply BitVec.le_def.mpr
        rw [nextNat]
        rw [rankEq] at done
        omega
      simp [condition,evalHOLFinite,evalHOLExact,evalListHOLExact,localI,localN,wordOpHOL,wordOp,valueIsWord,valueWord,done,Compiler.Encoders.Asm.wordCmpHOL]
      exact below
  have step : ∀ current : PanSemStateFiniteExact 64 F, invariant current → 0 < rank current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current memeqWord8Step = (none,post) ∧ invariant post ∧ rank post < rank current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           evaluateHOLFiniteState current memeqWord8Step = (some result,post))) := by
    rintro current ⟨⟨i,localI,inside⟩,localN⟩ positive _
    have rankEq : rank current = (size.toNat - i.toNat) / 8 := by simp [rank,memeqWord8Rank,localI]
    have below : i.toNat + 8 ≤ size.toNat := by rw [rankEq] at positive; omega
    have nextNat : (i + 8).toNat = i.toNat + 8 := by
      rw [BitVec.toNat_add_of_lt (by change i.toNat + 8 < 2 ^ 64; omega)]
      rfl
    obtain ⟨result,post,run,clock,outcome⟩ := evaluate_readCheckAdvanceStep memeq_word8_step_advances current i localI
    refine ⟨post,by omega,by omega,?_⟩
    rcases outcome with ⟨rfl,nextLocal,locals⟩ | failed | returned
    · have valid : invariant post := ⟨⟨i+8,nextLocal,by rw [nextNat]; omega⟩,(locals (ofString "n") (by decide)).trans localN⟩
      have rankPost : rank post = (size.toNat - (i + 8).toNat) / 8 := by simp [rank,memeqWord8Rank,nextLocal]
      exact Or.inl ⟨run,valid,by rw [rankPost,rankEq,nextNat]; omega⟩
    · subst result
      exact Or.inr ⟨.error,by simp,by simp,by simp,run⟩
    · subst result
      exact Or.inr ⟨.returned (.val (.word 0)),by simp,by simp,by simp,run⟩
  have initialRank : rank state = (size.toNat - index.toNat) / 8 := by simp [rank,memeqWord8Rank,initial]
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed⟩ := evaluate_ranked_loop_returns_invariant
    condition memeqWord8Step invariant rank 0 guard (by intro current valid; exact valid)
    (by intro current; rfl) step state ⟨⟨index,initial,bounded⟩,nLocal⟩
    (by simp only [Nat.zero_add,Nat.mul_one,initialRank]; omega)
  rw [source_memeq_word8_loop]
  exact ⟨result,post,run,(by simp only [Nat.zero_add,Nat.mul_one,initialRank] at cost; omega),remaining,noTimeout,completed⟩

#print axioms evaluate_memeq_word8_bounded_cap
end InitECandidate.Runtime
