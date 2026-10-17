import InitECandidate.Runtime.MemcpyAlignedSuffix
import InitECandidate.Runtime.ByteAdvanceStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual unaligned eight-byte copy step consists of eight stores and
one final index advance, including all possible memory failures. -/
theorem memcpyByte8Body_supported : ByteAdvanceStep (ofString "i") 8 memcpyByte8Body := by
  apply ByteAdvanceStep.store
  apply ByteAdvanceStep.store
  apply ByteAdvanceStep.store
  apply ByteAdvanceStep.store
  apply ByteAdvanceStep.store
  apply ByteAdvanceStep.store
  apply ByteAdvanceStep.store
  apply ByteAdvanceStep.store
  exact ByteAdvanceStep.advance

theorem evaluate_memcpy_byte8_progress {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    ∃ result post, evaluateHOLFiniteState state memcpyByte8Body = (result,post) ∧ post.clock = state.clock ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      ((result = none ∧ post.locals.lookup (ofString "i") = some (.val (.word (index + 8)))) ∨ result = some .error) := by
  exact evaluate_byteAdvanceStep memcpyByte8Body_supported state index binding

/-- For a heap-sized copy, the enabled block guard ensures a nonwrapping
index advance and a strictly decreasing remaining-byte rank. -/
theorem memcpy_byte8_rank (index size : BitVec 64)
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (enabled : (index + 8).toNat ≤ size.toNat) :
    (index + 8).toNat = index.toNat + 8 ∧ (index + 8).toNat ≤ size.toNat ∧
      size.toNat - (index + 8).toNat < size.toNat - index.toNat := by
  have next : (index + 8).toNat = index.toNat + 8 := by
    rw [BitVec.toNat_add_of_lt (by change index.toNat + 8 < 2^64; omega)]
    rfl
  exact ⟨next,enabled,by omega⟩

#print axioms memcpyByte8Body_supported
#print axioms evaluate_memcpy_byte8_progress
#print axioms memcpy_byte8_rank
end InitECandidate.Runtime
