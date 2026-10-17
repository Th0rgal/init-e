import InitECandidate.Runtime.HashTableReadyIntervalFrame
import InitECandidate.Runtime.FrameHalt
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Disjoint word stores preserve ready tables at every key width. -/
theorem HashTableReady.after_word_outside {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items destination value : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (outside : destination.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ destination.toNat) :
    HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer
      (sourceWriteWord state destination value) := by
  apply ready.interval_frame state (sourceWriteWord state destination value) keyLength table pointer keys stride capacity used values order orderPos items bits
  · intro address lower upper
    have different : address ≠ destination := by
      intro same
      have equal := congrArg BitVec.toNat same
      rcases outside with before | after <;> omega
    change (if address = destination then HolWordLab.word value else _) = _
    rw [if_neg different]
  · rfl
  · rfl
  · rfl
  · rfl

#print axioms HashTableReady.after_word_outside
end InitECandidate.Runtime
