import InitECandidate.Runtime.MemeqByte1Bound
import InitECandidate.Runtime.MemeqLoopSteps
import InitECandidate.Runtime.RankedLoopReturnsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original single-byte comparison loop uses at most n source ticks
for lengths up to the heap cap, including early mismatch returns and invalid memory. -/
theorem evaluate_memeq_byte1_bounded_cap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (size index : BitVec 64)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (nLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (bounded : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496) (ticks : size.toNat ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state memeqByte1Loop = (result,post) ∧
      state.clock ≤ post.clock + size.toNat ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → MemeqByteInvariant size post ∧ memeqByteRank size post = 0) := by
  let invariant := MemeqByteInvariant (F := F) size
  let rank := memeqByteRank (F := F) size
  let condition : ExpHOL 64 := .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))
  have guard : ∀ current : PanSemStateFiniteExact 64 F, invariant current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) condition =
        some (.val (.word (if rank current = 0 then 0 else 1))) := by
    rintro current ⟨⟨i,localI,inside⟩,localN⟩
    have rankEq : rank current = size.toNat - i.toNat := by simp [rank,memeqByteRank,localI]
    by_cases done : i.toNat = size.toNat
    · have equal : i = size := BitVec.eq_of_toNat_eq done
      have zero : rank current = 0 := by rw [rankEq,done]; omega
      simp [condition,evalHOLFinite,evalHOLExact,localI,localN,equal,zero,Compiler.Encoders.Asm.wordCmpHOL]
    · have positive : rank current ≠ 0 := by rw [rankEq]; omega
      have below : i < size := BitVec.lt_def.mpr (by omega)
      simp [condition,evalHOLFinite,evalHOLExact,localI,localN,positive,Compiler.Encoders.Asm.wordCmpHOL,below]
  have step : ∀ current : PanSemStateFiniteExact 64 F, invariant current → 0 < rank current → 0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current memeqByte1Step = (none,post) ∧ invariant post ∧ rank post < rank current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           evaluateHOLFiniteState current memeqByte1Step = (some result,post))) := by
    rintro current ⟨⟨i,localI,inside⟩,localN⟩ positive _
    have rankEq : rank current = size.toNat - i.toNat := by simp [rank,memeqByteRank,localI]
    have below : i.toNat < size.toNat := by rw [rankEq] at positive; omega
    have nextNat : (i + 1).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change i.toNat + 1 < 2 ^ 64; omega)]
      rfl
    obtain ⟨result,post,run,clock,outcome⟩ := evaluate_memeq_byte1_step current i localI
    refine ⟨post,by omega,by omega,?_⟩
    rcases outcome with ⟨rfl,nextLocal,locals⟩ | failed | returned
    · have valid : invariant post := ⟨⟨i+1,nextLocal,by rw [nextNat]; omega⟩,(locals (ofString "n") (by decide)).trans localN⟩
      have rankPost : rank post = size.toNat - (i + 1).toNat := by simp [rank,memeqByteRank,nextLocal]
      exact Or.inl ⟨run,valid,by rw [rankPost,rankEq,nextNat]; omega⟩
    · subst result
      exact Or.inr ⟨.error,by simp,by simp,by simp,run⟩
    · subst result
      exact Or.inr ⟨.returned (.val (.word 0)),by simp,by simp,by simp,run⟩
  have initialRank : rank state = size.toNat - index.toNat := by simp [rank,memeqByteRank,initial]
  obtain ⟨result,post,run,cost,remaining,noTimeout,completed⟩ := evaluate_ranked_loop_returns_invariant
    condition memeqByte1Step invariant rank 0 guard (by intro current valid; exact valid)
    (by intro current; rfl) step state ⟨⟨index,initial,bounded⟩,nLocal⟩
    (by simp only [Nat.zero_add,Nat.mul_one,initialRank]; omega)
  rw [source_memeq_byte1_loop]
  exact ⟨result,post,run,(by simp only [Nat.zero_add,Nat.mul_one,initialRank] at cost; omega),remaining,noTimeout,completed⟩

#print axioms evaluate_memeq_byte1_bounded_cap
end InitECandidate.Runtime
