import InitECandidate.Runtime.CanonicalSourceEntryFields
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Compiler.Backend

theorem canonical_arena_index (address : BitVec 64) (aligned : address.toNat % 8 = 0)
    (lower : 2713714688 ≤ address.toNat) (upper : address.toNat < 33806089496) :
    ∃ i, i < ((stackStart - sourceBase) / 8 - globalsWords) ∧
      address = BitVec.ofNat 64 sourceBase + BitVec.ofNat 64 i * StackRemove.bytesInWord 64 := by
  refine ⟨(address.toNat - 2701131776) / 8, ?_, ?_⟩
  · have count : ((stackStart - sourceBase) / 8 - globalsWords) = 3888119715 := by
      decide_cbv
    rw [count]
    omega
  · have arithmetic : address.toNat = 2701131776 + (address.toNat - 2701131776) / 8 * 8 := by omega
    calc
      address = BitVec.ofNat 64 address.toNat := by simp
      _ = BitVec.ofNat 64 (2701131776 + (address.toNat - 2701131776) / 8 * 8) := congrArg (BitVec.ofNat 64) arithmetic
      _ = _ := by rw [BitVec.ofNat_add, BitVec.ofNat_mul]; rfl

#print axioms canonical_arena_index

/-- The real source arena contains aligned word cells, rather than every
byte address. This is the domain available to initialization stores. -/
theorem canonical_source_aligned_arena (input : Guest.InputBlob)
    (address : BitVec 64) (aligned : address.toNat % 8 = 0)
    (lower : 2713714688 ≤ address.toNat)
    (upper : address.toNat < 33806089496) :
    (sourceInitialState input).memaddrs address := by
  have member := canonical_arena_index address aligned lower upper
  exact (StackRemove.mem_addresses ((stackStart - sourceBase) / 8 - globalsWords)
    (BitVec.ofNat 64 sourceBase) address).mpr member

theorem canonical_unrenamed_aligned_arena (input : Guest.InputBlob)
    (address : BitVec 64) (aligned : address.toNat % 8 = 0)
    (lower : 2713714688 ≤ address.toNat)
    (upper : address.toNat < 33806089496) :
    (canonicalUnrenamedSourceEntry input).memaddrs address := by
  rw [canonical_unrenamed_source_fields]
  exact canonical_source_aligned_arena input address aligned lower upper

#print axioms canonical_source_aligned_arena
#print axioms canonical_unrenamed_aligned_arena
end InitECandidate.Runtime
