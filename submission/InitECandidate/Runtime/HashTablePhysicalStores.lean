import InitECandidate.Runtime.HashTablePhysicalFrame
import InitECandidate.Runtime.HashTableReadyByteOutside
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A store in a relocation gap preserves every live part of the table. -/
theorem HashTableReady.after_word_physical {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items address value : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (outside : ¬tablePhysicalRegion table keys stride capacity used values order orderPos address) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer (sourceWriteWord state address value) := by
  apply ready.physical_frame state _ keyLength table pointer keys stride capacity used values order orderPos items bits
  · intro watched member
    have different : watched ≠ address := by intro same; subst watched; exact outside member
    simp only [sourceWriteWord]
    simp
    intro equal
    exact False.elim (different equal)
  · rfl
  · rfl
  · rfl
  · rfl

/-- Byte writes must miss all live regions at their aligned containing word. -/
theorem HashTableReady.after_byte_physical {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items address value cell : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (outside : ¬tablePhysicalRegion table keys stride capacity used values order orderPos (panByteAlignHOL address)) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer (sourceWriteByte state address value cell) := by
  exact ready.after_word_physical state keyLength table pointer keys stride capacity used values order orderPos items (panByteAlignHOL address) _ bits outside

#print axioms HashTableReady.after_word_physical
#print axioms HashTableReady.after_byte_physical
end InitECandidate.Runtime
