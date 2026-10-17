import InitECandidate.Runtime.HashTableReadyFrame32
import InitECandidate.Runtime.FrameHalt
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A journal word store disjoint from the table's observed cells preserves
all reusable facts; unrelated key bytes and external memory may change. -/
theorem HashTableReady32.after_word {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items destination value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (header : ∀ offset ∈ ([0,8,16,24,32,40,48,56,64] : List Nat), table + BitVec.ofNat 64 offset ≠ destination)
    (occupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → panByteAlignHOL (used + slot) ≠ destination)
    (valuesSeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → values + slot * 8 ≠ destination)
    (reverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → orderPos + slot * 8 ≠ destination)
    (forward : ∀ position : BitVec 64, position.toNat < items.toNat → order + position * 8 ≠ destination) :
    HashTableReady32 table keys stride capacity used values order orderPos items bits pointer
      (sourceWriteWord state destination value) := by
  apply ready.framed state (sourceWriteWord state destination value)
    table pointer keys stride capacity used values order orderPos items bits
  · intro offset member
    change (if table + BitVec.ofNat 64 offset = destination then HolWordLab.word value else _) = _
    rw [if_neg (header offset member)]
  · intro slot inside
    simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,occupancy slot inside]
    rfl
  · intro slot inside
    change (if values + slot * 8 = destination then HolWordLab.word value else _) = _
    rw [if_neg (valuesSeparate slot inside)]
  · intro slot inside
    change (if orderPos + slot * 8 = destination then HolWordLab.word value else _) = _
    rw [if_neg (reverse slot inside)]
  · intro position inside
    change (if order + position * 8 = destination then HolWordLab.word value else _) = _
    rw [if_neg (forward position inside)]
  · rfl
  · rfl
  · rfl

#print axioms HashTableReady32.after_word
end InitECandidate.Runtime
