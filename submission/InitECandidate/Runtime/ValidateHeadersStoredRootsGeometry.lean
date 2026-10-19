import InitECandidate.Runtime.ValidateHeadersStoredRootsStep
/-!
The separation of a stored record from the tail's writes comes from the concrete layout.

The guest lays the shared buffers out in one order and the keccak workspace in another, and both
matter.  Below the arena ceiling sit the frame, the scratch area, the keccak state and the pad;
above the ceiling sit the slice-witness table (`array`), then the header-pointer buffer (`hs`),
then the hash buffer (`hashes`); the heap the loop allocates from starts above all of them.

* the pointer buffer ends before the hash buffer (`hs + count * 8 ≤ hashes`);
* the keccak state and the pad end before the pointer buffer
  (`keccakState + 200`, `keccakPad + 136 ≤ hs`);
* the hash buffer, and with it its last output slot, ends at the fixed floor
  `hashes + count * 32 + 32`, which is where every stored record starts.

The tail writes exactly three things: the store target `hs + index * 8`, the keccak state and pad
words, and the output slot `hashes + index * 32`.  For a stored pointer cell
(`slot < index < count`) the cell is above the state and pad (`mwin_below` from
`keccakState + 200 ≤ hs`) and below the output slot (`mwin_above` from
`hs + count * 8 ≤ hashes`).  For a stored record's root word the record starts at the floor, so
the root word is above the state and pad and above the whole output window (`mwin_below` from
`hashes + count * 32 + 32 ≤ prior`).

Nothing here uses the moving live heap frontier: a stored record is separated from the tail's
writes by its own fixed lower bound (the floor), exactly as the lead asked.  The live frontier is
used only for the record's extent, which is what the parent declaration needs.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 500000

/-- A stored pointer cell below the current index is separated from the tail's store target, from
the keccak state and pad windows and from the current output slot. -/
theorem validate_headers_stored_roots_separation {F : Type}
    (s : PanSemStateFiniteExact 64 F) (hs hashes index count keccakState keccakPad : BitVec 64)
    (filled : Nat)
    (inside : index.toNat < count.toNat)
    (bufferBeforeHashes : hs.toNat + count.toNat * 8 ≤ hashes.toNat)
    (stateBeforeHs : keccakState.toNat + 200 ≤ hs.toNat) (padBeforeHs : keccakPad.toNat + 136 ≤ hs.toNat)
    (hsBufferBound : hs.toNat + count.toNat * 8 + 8 ≤ 33806089496)
    (hashAligned : hashes.toNat % 8 = 0)
    (hashBufferBound : hashes.toNat + count.toNat * 32 + 32 ≤ 33806089496)
    (slot : BitVec 64) (within : slot.toNat < filled) (slotBound : filled ≤ count.toNat)
    (older : filled ≤ index.toNat) :
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

/-- A stored record's root word is separated from the tail's store target and write windows: the
record starts at the fixed floor, so its root word is above the whole pointer and hash buffers and
above the output slot, while the keccak state and pad sit below the floor as well. -/
theorem validate_headers_stored_root_separation {F : Type}
    (hs hashes index count keccakState keccakPad prior : BitVec 64) (frontier : Nat)
    (inside : index.toNat < count.toNat)
    (aboveFloor : hashes.toNat + count.toNat * 32 + 32 ≤ prior.toNat)
    (extent : prior.toNat + 248 ≤ frontier) (frontierBound : frontier ≤ 33806089496)
    (stateBelowFloor : keccakState.toNat + 200 ≤ hashes.toNat + count.toNat * 32 + 32)
    (padBelowFloor : keccakPad.toNat + 136 ≤ hashes.toNat + count.toNat * 32 + 32)
    (bufferBeforeHashes : hs.toNat + count.toNat * 8 ≤ hashes.toNat)
    (hashBufferBound : hashes.toNat + count.toNat * 32 + 32 ≤ 33806089496) :
    (hs + index * 8 ≠ prior + 32#64 ∧ ¬ MWin keccakState 200 (prior + 32#64) ∧
        ¬ MWin keccakPad 136 (prior + 32#64) ∧ ¬ MWin (hashes + index * 32) 32 (prior + 32#64)) := by
  have rootAddr : (prior + 32#64).toNat = prior.toNat + 32 := by
    rw [BitVec.toNat_add_of_lt (by change prior.toNat + 32 < 2^64; omega)]
    rfl
  have stateAtRoot : keccakState.toNat + 200 ≤ (prior + 32#64).toNat := by rw [rootAddr]; omega
  have padAtRoot : keccakPad.toNat + 136 ≤ (prior + 32#64).toNat := by rw [rootAddr]; omega
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
  have hashNat : (hashes + index * 32).toNat = hashes.toNat + index.toNat * 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [hashProduct]; omega),hashProduct]
  have belowRoot : (hashes + index * 32).toNat + 32 ≤ (prior + 32#64).toNat := by
    rw [hashNat,rootAddr]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · intro same
    have levels := congrArg BitVec.toNat same
    rw [storeAddr,rootAddr] at levels
    omega
  · exact mwin_below (D := keccakState) (N := 200) (w := prior + 32#64) stateAtRoot
  · exact mwin_below (D := keccakPad) (N := 136) (w := prior + 32#64) padAtRoot
  · exact mwin_below (D := hashes + index * 32) (N := 32) (w := prior + 32#64) belowRoot

#print axioms validate_headers_stored_root_separation
end InitECandidate.Runtime
