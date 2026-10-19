import InitECandidate.Runtime.ValidateHeadersStoredRootsStep
/-!
The per-address separation of one iteration comes from the concrete arena, not from a callback.

For a stored parent record the three keccak facts and the store-slot separation all follow from
the ceiling alone.  Everything the loop already keeps below the ceiling is below every record
root, and everything a record owns starts at or above it:

* the pointer buffer ends below the ceiling (`hs + count * 8 + 8 ≤ ceiling`);
* the hash buffer and its last output slot end below the ceiling
  (`hashes + count * 32 + 32 ≤ ceiling`);
* the keccak state and the pad end below the ceiling (`keccakState + 200`, `keccakPad + 136`);
* every stored record starts at or above the ceiling (`ceiling ≤ prior`), which is the arena
  containment the validation loop already has for its allocations.

Hence `hs + index * 8 ≠ prior + 32`, and the state, the pad and the output slot never intersect
`prior + 32`; for the pointer buffer's own slot `hs + index * 8 ≠ hs + slot * 8` since both are
below the ceiling and strictly ordered.  No per-iteration hypothesis remains: these are `∃`-free
consequences of the state shape plus the two buffer bounds.

The live frontier is not used here at all: old records are separated by their own lower bound
(`ceiling ≤ prior`), exactly as the lead asked.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/-- The two buffer bounds and the arena containment separate every stored record from the tail's
write set, per address, at any index below `count`. -/
theorem validate_headers_stored_roots_separation {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hs hashes index count keccakState keccakPad : BitVec 64)
    (ceiling filled : Nat)
    (inside : index.toNat < count.toNat) (ceilingBound : ceiling < 2^64)
    (slotBufferBelow : hs.toNat + count.toNat * 8 + 8 ≤ ceiling)
    (hashBufferBelow : hashes.toNat + count.toNat * 32 + 32 ≤ ceiling)
    (stateBeforeHs : keccakState.toNat + 200 ≤ hs.toNat) (padBeforeHs : keccakPad.toNat + 136 ≤ hs.toNat)
    (hashAligned : hashes.toNat % 8 = 0)
    (slot : BitVec 64) (within : slot.toNat < filled) (slotBound : filled ≤ count.toNat)
    (older : filled ≤ index.toNat) (hsBeforeHashes : hs.toNat ≤ hashes.toNat) :
    (hs + index * 8 ≠ hs + slot * (8#64) ∧ ¬ MWin keccakState 200 (hs + slot * (8#64)) ∧
        ¬ MWin keccakPad 136 (hs + slot * (8#64)) ∧
        ¬ MWin (hashes + index * 32) 32 (hs + slot * (8#64))) := by
  have slotBelow : slot.toNat < count.toNat := by omega
  have slotProduct : (slot * (8#64)).toNat = slot.toNat * 8 := by
    rw [BitVec.toNat_mul_of_lt (by change slot.toNat * 8 < 2^64; omega)]
    rfl
  have slotAddr : (hs + slot * (8#64)).toNat = hs.toNat + slot.toNat * 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [slotProduct]; omega),slotProduct]
  have countWidth8 : count.toNat * 8 < 2^64 := by omega
  have countWidth32 : count.toNat * 32 < 2^64 := by omega
  have stateAtSlot : keccakState.toNat + 200 ≤ (hs + slot * (8#64)).toNat := by
    rw [slotAddr]
    omega
  have padAtSlot : keccakPad.toNat + 136 ≤ (hs + slot * (8#64)).toNat := by
    rw [slotAddr]
    omega
  have indexProduct : (index * 8).toNat = index.toNat * 8 := by
    rw [BitVec.toNat_mul_of_lt (by change index.toNat * 8 < 2^64; omega)]
    rfl
  have indexAddr : (hs + index * 8).toNat = hs.toNat + index.toNat * 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [indexProduct]; omega),indexProduct]
  have hashProduct : (index * 32).toNat = index.toNat * 32 := by
    rw [BitVec.toNat_mul_of_lt (by change index.toNat * 32 < 2^64; omega)]
    rfl
  have hashNat : (hashes + index * 32).toNat = hashes.toNat + index.toNat * 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [hashProduct]; omega),hashProduct]
  have hashWindowAligned : (hashes + index * 32).toNat % 8 = 0 := by
    obtain ⟨quotient, hquotient⟩ := Nat.dvd_of_mod_eq_zero hashAligned
    rw [hashNat]
    exact Nat.mod_eq_zero_of_dvd ⟨quotient + index.toNat * 4, by omega⟩
  have slotBeforeHash : (hs + slot * (8#64)).toNat < (hashes + index * 32).toNat := by
    rw [slotAddr,hashNat]
    omega
  have hashFit : (hashes + index * 32).toNat + 32 < 2^64 := by rw [hashNat]; omega
  refine ⟨?_,?_,?_,?_⟩
  · intro same
    have levels := congrArg BitVec.toNat same
    rw [indexAddr,slotAddr] at levels
    omega
  · exact mwin_below (D := keccakState) (N := 200) (w := hs + slot * (8#64)) stateAtSlot
  · exact mwin_below (D := keccakPad) (N := 136) (w := hs + slot * (8#64)) padAtSlot
  · exact mwin_above (D := hashes + index * 32) (N := 32) (w := hs + slot * (8#64))
      slotBeforeHash hashWindowAligned hashFit

#print axioms validate_headers_stored_roots_separation

/-- A stored record's root word is separated from the tail's write set by the record's own
lower bound `ceiling ≤ prior`. -/
theorem validate_headers_stored_root_separation {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hs hashes index count keccakState keccakPad prior : BitVec 64)
    (ceiling : Nat)
    (inside : index.toNat < count.toNat) (ceilingBound : ceiling < 2^64)
    (slotBufferBelow : hs.toNat + count.toNat * 8 + 8 ≤ ceiling)
    (hashBufferBelow : hashes.toNat + count.toNat * 32 + 32 ≤ ceiling)
    (stateBelow : keccakState.toNat + 200 ≤ ceiling) (padBelow : keccakPad.toNat + 136 ≤ ceiling)
    (priorAbove : ceiling ≤ prior.toNat) (priorBound : prior.toNat + 248 ≤ 33806089496) :
    (hs + index * 8 ≠ prior + 32#64 ∧ ¬ MWin keccakState 200 (prior + 32#64) ∧
        ¬ MWin keccakPad 136 (prior + 32#64) ∧ ¬ MWin (hashes + index * 32) 32 (prior + 32#64)) := by
  have rootAddr : (prior + 32#64).toNat = prior.toNat + 32 := by
    rw [BitVec.toNat_add_of_lt (by change prior.toNat + 32 < 2^64; omega)]
    rfl
  have rootAbove : ceiling ≤ (prior + 32#64).toNat := by rw [rootAddr]; omega
  have stateAtRoot : keccakState.toNat + 200 ≤ (prior + 32#64).toNat := by omega
  have padAtRoot : keccakPad.toNat + 136 ≤ (prior + 32#64).toNat := by omega
  have countWidth8 : count.toNat * 8 < 2^64 := by omega
  have countWidth32 : count.toNat * 32 < 2^64 := by omega
  have indexProduct : (index * 8).toNat = index.toNat * 8 := by
    rw [BitVec.toNat_mul_of_lt (by change index.toNat * 8 < 2^64; omega)]
    rfl
  have storeAddr : (hs + index * 8).toNat = hs.toNat + index.toNat * 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [indexProduct]; omega),indexProduct]
  have hashProduct : (index * 32).toNat = index.toNat * 32 := by
    rw [BitVec.toNat_mul_of_lt (by change index.toNat * 32 < 2^64; omega)]
    rfl
  have hashAddr : (hashes + index * 32).toNat + 32 ≤ ceiling := by
    rw [BitVec.toNat_add_of_lt (by rw [hashProduct]; omega),hashProduct]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · intro same
    have levels := congrArg BitVec.toNat same
    rw [storeAddr,rootAddr] at levels
    omega
  · exact mwin_below (D := keccakState) (N := 200) (w := prior + 32#64) stateAtRoot
  · exact mwin_below (D := keccakPad) (N := 136) (w := prior + 32#64) padAtRoot
  · exact mwin_below (D := hashes + index * 32) (N := 32) (w := prior + 32#64)
      (by rw [rootAddr]; omega)

#print axioms validate_headers_stored_root_separation
end InitECandidate.Runtime
