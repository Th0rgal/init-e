import InitECandidate.Runtime.ValidateHeadersHashNormalFrame
import InitECandidate.Runtime.NodedbWindowGeometry
import InitECandidate.Runtime.AccountOptionalArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Actual bounded hash-buffer geometry supplies alignment and separation of
the hash call's write windows from every older word below the header-pointer buffer. -/
theorem validate_headers_hash_geometry (hashes index count keccakState keccakPad upper : BitVec 64) (ceiling : Nat)
    (inside : index.toNat < count.toNat)
    (bufferBound : hashes.toNat + count.toNat * 32 + 32 ≤ 33806089496)
    (hashAligned : hashes.toNat % 8 = 0)
    (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (upperBefore : upper.toNat ≤ hashes.toNat) :
    (hashes + index * 32).toNat = hashes.toNat + index.toNat * 32 ∧
      (hashes + index * 32).toNat % 8 = 0 ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < upper.toNat →
        ¬ MWin keccakState 200 address ∧ ¬ MWin keccakPad 136 address ∧ ¬ MWin (hashes + index * 32) 32 address) := by
  have productNat : (index * 32).toNat = index.toNat * 32 := by
    rw [BitVec.toNat_mul_of_lt (by change index.toNat * 32 < 2^64; omega)]
    rfl
  have outputNat : (hashes + index * 32).toNat = hashes.toNat + index.toNat * 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [productNat]; omega),productNat]
  have outputAligned : (hashes + index * 32).toNat % 8 = 0 := by
    rw [outputNat]
    simp [Nat.add_mod,Nat.mul_mod,hashAligned]
  refine ⟨outputNat,outputAligned,?_⟩
  intro address lo hi
  refine ⟨mwin_below (by omega),mwin_below (by omega),?_⟩
  exact mwin_above (by rw [outputNat]; omega) outputAligned (by rw [outputNat]; omega)

#print axioms validate_headers_hash_geometry
end InitECandidate.Runtime
