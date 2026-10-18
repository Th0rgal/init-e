import InitECandidate.Runtime.ByteStoreMemoryFrame
namespace InitECandidate.Runtime
open Flapjack

theorem panByteStore_memory_other
    (memory updated : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address watched : BitVec 64) (byte : BitVec 8)
    (separate : watched ≠ panByteAlignHOL address)
    (stored : panMemStoreByteWord8HOL memory domain bigEndian address byte = some updated) :
    updated watched = memory watched := by
  cases cell : memory (panByteAlignHOL address) with
  | word value =>
    by_cases accessible : domain (panByteAlignHOL address)
    · simp [panMemStoreByteWord8HOL,cell,accessible] at stored
      rw [← stored]
      simp [separate]
    · simp [panMemStoreByteWord8HOL,cell,accessible] at stored

/-- The actual tail-first HOL byte writer preserves every watched word whose
aligned address is absent from the complete written byte interval. Failed
stores also preserve it, because they restore the original outer memory. -/
theorem panWriteBytearray_memory_other
    (bytes : List (BitVec 8)) (memory : BitVec 64 → HolWordLab 64)
    (domain : BitVec 64 → Prop) [DecidablePred domain] (bigEndian : Bool)
    (address watched : BitVec 64)
    (separate : ∀ offset : Nat, offset < bytes.length →
      watched ≠ panByteAlignHOL (address + BitVec.ofNat 64 offset)) :
    panWriteBytearrayWord8HOL address bytes memory domain bigEndian watched = memory watched := by
  induction bytes generalizing address with
  | nil => rfl
  | cons byte rest ih =>
    have headSeparate : watched ≠ panByteAlignHOL address := by simpa using separate 0 (by simp)
    have tailSeparate : ∀ offset : Nat, offset < rest.length →
        watched ≠ panByteAlignHOL (address + 1 + BitVec.ofNat 64 offset) := by
      intro offset inside
      have original := separate (offset + 1) (by simp; omega)
      have addresses : address + 1 + BitVec.ofNat 64 offset = address + BitVec.ofNat 64 (offset + 1) := by
        rw [BitVec.ofNat_add,BitVec.add_assoc]
        congr 1
        exact BitVec.add_comm _ _
      rw [addresses]
      exact original
    have tailFrame := ih (address + 1) tailSeparate
    rw [panWriteBytearrayWord8HOL]
    cases stored : panMemStoreByteWord8HOL
        (panWriteBytearrayWord8HOL (address + 1) rest memory domain bigEndian) domain bigEndian address byte with
    | none => rfl
    | some updated =>
      exact (panByteStore_memory_other _ updated domain bigEndian address watched byte headSeparate stored).trans tailFrame

#print axioms panByteStore_memory_other
#print axioms panWriteBytearray_memory_other
end InitECandidate.Runtime
