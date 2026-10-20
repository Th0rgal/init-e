import InitECandidate.Runtime.ValidateHeadersStoredRootsNormalStep
/-!
The stored-roots invariant refined by the rank-aware 624-byte heap room.

`ValidateHeadersStoredRootsRoomedInvariant` is the existing invariant together with: every typed
value of `heap_ptr` leaves room for the current iteration and one 624-byte block per remaining
one.  The normal enabled step preserves it, because the strengthened step returns the entry heap
and the exit heap with strict growth, and lookup injectivity equates any typed exit heap with the
one the step reports.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- The stored-roots invariant plus rank-aware heap room. -/
def ValidateHeadersStoredRootsRoomedInvariant {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ValidateHeadersStoredRootsInvariant e s rank ∧
  ∀ heap : BitVec 64, s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) →
    heap.toNat + (rank + 1) * headerCarryRoom ≤ 33806089496

/-- One enabled normal actual iteration preserves the roomed invariant with a strictly smaller
rank.  The plain room the underlying step wants is the refined room for the current block, and
the refined room at the exit follows from strict growth under a smaller rank. -/
theorem validate_headers_stored_roots_roomed_step {F : Type} (e : ValidateHeadersFirstEnvironment)
    (s post : PanSemStateFiniteExact 64 F) (rank : Nat)
    (hsAbove : e.ceiling ≤ e.hs.toNat)
    (bufferBeforeHashes : e.hs.toNat + e.count.toNat * 8 ≤ e.hashes.toNat)
    (refined : ValidateHeadersStoredRootsRoomedInvariant e s rank)
    (code : s.code = originalRuntimeCode) (w : BitVec 64)
    (condition : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      validateHeadersFirstCondition = some (.val (.word w)))
    (nonzero : w ≠ 0)
    (budget : headerDecoderBodyCost e.inputLimit + 1 + (e.inputLimit * 20 + 125) ≤ s.clock)
    (normal : evaluateHOLFiniteState s validateHeadersFirstBody = (none,post)) :
    ∃ nextRank, nextRank < rank ∧ ValidateHeadersStoredRootsRoomedInvariant e post nextRank := by
  have plainRoom : ∀ heap : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) →
      heap.toNat + headerCarryRoom ≤ 33806089496 := fun heap binding =>
    Nat.le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_left headerCarryRoom (Nat.succ_pos rank)) heap.toNat)
      (refined.2 heap binding)
  obtain ⟨nextRank,smaller,kept,oldHeap,newHeap,oldBinding,newBinding,growth⟩ :=
    validate_headers_stored_roots_invariant_step e s post rank hsAbove bufferBeforeHashes refined.1
      code w condition nonzero plainRoom budget normal
  refine ⟨nextRank,smaller,kept,fun heap binding => ?_⟩
  have heapEq : heap = newHeap := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (binding.symm.trans newBinding)))
  rw [heapEq]
  have oldRoom := refined.2 oldHeap oldBinding
  have decreasing : nextRank + 1 ≤ rank := by omega
  have monotone : (nextRank + 1) * headerCarryRoom ≤ rank * headerCarryRoom :=
    Nat.mul_le_mul_right headerCarryRoom decreasing
  unfold headerCarryRoom at *
  omega

#print axioms validate_headers_stored_roots_roomed_step
end InitECandidate.Runtime
