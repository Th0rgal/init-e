import InitECandidate.Runtime.CanonicalAlignedArena
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Compiler.Backend
/-- The authoritative challenge domain consists of aligned word cells. -/
theorem ordinaryDomain_word_aligned (address : BitVec 64) (valid : ordinaryDomain address) :
    address.toNat%8=0 := by
  rw [ordinaryDomain,StackRemove.mem_addresses] at valid
  obtain ⟨i,inside,rfl⟩ := valid
  norm_num [sourceBase,stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords,
    StackRemove.bytesInWord,BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat] at inside ⊢

/-- An arena containing every byte address cannot describe the authoritative
ordinary domain on any interval containing two consecutive addresses. -/
theorem ordinaryDomain_not_all_address_arena (lower upper : Nat)
    (room : lower+2≤upper) (noWrap : upper≤2^64) :
    ¬ (∀ address : BitVec 64, lower≤address.toNat → address.toNat<upper → ordinaryDomain address) := by
  intro arena
  have firstNat : (BitVec.ofNat 64 lower).toNat=lower := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have nextNat : (BitVec.ofNat 64 (lower+1)).toNat=lower+1 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have first := ordinaryDomain_word_aligned (BitVec.ofNat 64 lower)
    (arena _ (by rw [firstNat]) (by rw [firstNat];omega))
  have next := ordinaryDomain_word_aligned (BitVec.ofNat 64 (lower+1))
    (arena _ (by rw [nextNat];omega) (by rw [nextNat];omega))
  rw [firstNat] at first
  rw [nextNat] at next
  omega
#print axioms ordinaryDomain_word_aligned
#print axioms ordinaryDomain_not_all_address_arena
end InitECandidate.Runtime
