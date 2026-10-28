import InitECandidate.Proofs.Op5.MemoryDomain
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRel
import Flapjack.Compiler.Backend.LabToTarget.InstFrame

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Encoders.Asm

/-- The actual WordToStack relation transports the union domain unchanged.
No global equality of source and target states is assumed. -/
theorem wordToStack_twoRegion {C F : Type} (ac : AsmConfigExact 64)
    (k f f' extra : Nat) (lens : List Nat)
    (s : WordSemStateFiniteExact 64 (Nat × C) F)
    (t : StackSemStateFiniteExact 64 C F) (sl sh pl ph : Nat)
    (rel : WordToStackProofs.stateRel ac k f f' s t lens extra)
    (domain : ∀ a, s.mdomain a = true ↔ twoRegion sl sh pl ph a) :
    (∀ a, t.mdomain a = true ↔ twoRegion sl sh pl ph a) ∧
      (∀ a, twoRegion sl sh pl ph a → t.memory a = s.memory a) := by
  rcases rel with ⟨_,_,_,_,_,_,_,hm,hd,_⟩
  constructor
  · simpa only [hd] using domain
  · intro a _
    exact congrFun hm a

/-- Ordinary byte domain used below the Lab/target boundary. Unlike the word
predicate, it includes each of the eight bytes in an aligned cell. -/
def twoRegionBytes (sl sh pl ph : Nat) (a : BitVec 64) : Prop :=
  region sl sh a ∨ region pl ph a

/-- The existing target code/buffer frame theorem applies to the extended byte
memory domain. Code bytes outside both regions survive ordinary writes in either. -/
theorem target_code_frame (sl sh pl ph : Nat) (pc : BitVec 64)
    (code : List (BitVec 8)) (before after : BitVec 64 → BitVec 8)
    (programDomain : BitVec 64 → Prop)
    (writes : ∀ a, ¬ InitE.Op5.twoRegionBytes sl sh pl ph a → after a = before a)
    (loaded : bytesInMemHOL pc code before programDomain (InitE.Op5.twoRegionBytes sl sh pl ph)) :
    bytesInMemHOL pc code after programDomain (InitE.Op5.twoRegionBytes sl sh pl ph) :=
  Compiler.Backend.LabToTarget.bytesInMem_frame pc code before after
    programDomain (InitE.Op5.twoRegionBytes sl sh pl ph) writes loaded

/-- A stack-confined target update preserves all eight bytes of every union
word cell, including the final cell directly below the stack boundary. -/
theorem target_stack_preserves_cell {S Q : Type} (mc : MachineConfig 64 S Q)
    (before after : S) (sl sh pl ph stackLo stackHi : Nat)
    (hs : sh ≤ stackLo) (hp : ph ≤ stackLo) (aligned : stackLo % 8 = 0)
    (noWrap : stackLo < 2^64)
    (writes : ∀ a, ¬ region stackLo stackHi a →
      mc.target.getByte after a = mc.target.getByte before a)
    (a : BitVec 64) (ha : twoRegion sl sh pl ph a) (j : Fin 8) :
    mc.target.getByte after (a + BitVec.ofNat 64 j.val) =
      mc.target.getByte before (a + BitVec.ofNat 64 j.val) := by
  have low : a.toNat + j.val < stackLo := by
    simp only [twoRegion,region] at ha
    have hj := j.isLt
    omega
  apply writes
  unfold region
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have hj := j.isLt; omega : j.val < 2^64),
    Nat.mod_eq_of_lt (by omega : a.toNat + j.val < 2^64)]
  omega

#print axioms wordToStack_twoRegion
#print axioms target_code_frame
#print axioms target_stack_preserves_cell
end InitE.Op5
