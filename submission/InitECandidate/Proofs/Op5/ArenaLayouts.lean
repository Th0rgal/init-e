import InitECandidate.Proofs.Op5.MemoryDomain
import InitE.SourceSemantics
import Flapjack.Compiler.Backend.LabToTarget.InstMem
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMemory

set_option maxRecDepth 2048

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Pancake.Proofs.PanToTarget

/-- Raw scratch bytes at the authoritative pinned guest layout. -/
def guestByteArena (a : BitVec 64) : Bool := decide (scratchStart ≤ a.toNat ∧ a.toNat < scratchEnd)

/-- The aligned word-cell starts used by compiler source states. -/
def guestWordArena (a : BitVec 64) : Prop :=
  guestByteArena a = true ∧ holByteAligned a = true

theorem guestWordArena_byte_relation (a : BitVec 64) :
    guestWordArena a ↔ guestByteArena a = true ∧ holByteAligned a = true := Iff.rfl

/-- The source's existing persistent domain is exactly its aligned byte interval. -/
theorem ordinaryDomain_interval (a : BitVec 64) :
    ordinaryDomain a ↔ a.toNat % 8 = 0 ∧ region sourceBase heapEnd a := by
  have eq := alignedInterval_eq_addresses (width := 64) (by right; rfl)
    (BitVec.ofNat 64 sourceBase) (BitVec.ofNat 64 heapEnd)
    (by rw [holByteAligned_iff_mod (by right; rfl : goodDimindex 64)]; decide)
    (by rw [holByteAligned_iff_mod (by right; rfl : goodDimindex 64)]; decide)
    (by decide)
  have count : (-1 * (BitVec.ofNat 64 sourceBase) + BitVec.ofNat 64 heapEnd).toNat /
      (64 / 8) = (stackStart - sourceBase) / 8 - globalsWords := by decide
  rw [count] at eq
  change StackRemove.addresses _ _ a ↔ _
  rw [← eq]
  simp only [holByteAligned_iff_mod (by right; rfl : goodDimindex 64)]
  simp only [region, BitVec.le_def, BitVec.lt_def, BitVec.toNat_ofNat]
  norm_num [sourceBase, heapEnd, stackStart, ramEnd, ramStart, ramSize, stackSize, globalsWords]

/-- The extended pinned domain is precisely the original persistent domain
union the guest's aligned scratch cells. Frozen source semantics are unchanged. -/
theorem guestDomain_union (a : BitVec 64) :
    guestDomain a ↔ ordinaryDomain a ∨ guestWordArena a := by
  rw [ordinaryDomain_interval]
  simp only [guestDomain, twoRegion, guestWordArena, guestByteArena, decide_eq_true_eq, region,
    holByteAligned_iff_mod (by right; rfl : goodDimindex 64)]
  tauto

/-- The pinned scratch does not overlap even the persistent region's globals
or physical stack: it lies strictly below the persistent initialization base. -/
theorem guestArena_below_initialization (a : BitVec 64) (ha : guestWordArena a) :
    a.toNat < sourceBase := by
  have hr : region scratchStart scratchEnd a := by
    exact (of_decide_eq_true ha.1 : scratchStart ≤ a.toNat ∧ a.toNat < scratchEnd)
  have bound : scratchEnd ≤ sourceBase := by decide
  simp only [region] at hr
  omega

/-- At this pinned revision the requested numeric arena is already contained
in ordinaryDomain. Adding it as a union therefore preserves that exact domain. -/
theorem requested_union_ordinaryDomain (a : BitVec 64) :
    ordinaryDomain a ∨ (a.toNat % 8 = 0 ∧ region 0xa1001000 0xa1c00000 a) ↔
      ordinaryDomain a := by
  rw [ordinaryDomain_interval]
  have incl := requested_scratch_already_above_base a
  tauto

/-- The concrete scratch cells satisfy the compiler theorem's machine heap
separation guard when the installed persistent base is the pinned sourceBase. -/
theorem guestArena_machine_separation (base limit : BitVec 64)
    (baseEq : base = BitVec.ofNat 64 sourceBase) :
    ∀ a, guestWordArena a → ¬(base ≤ a ∧ a < limit) := by
  intro a ha ⟨hb, _⟩
  have low := guestArena_below_initialization a ha
  subst base
  have baseNat : (BitVec.ofNat 64 sourceBase).toNat = sourceBase := by decide
  rw [BitVec.le_def, baseNat] at hb
  omega

/-- Scratch ownership contains every byte of each aligned owned word, as
required by goodInitState at the physical machine boundary. -/
theorem guestByteArena_word_closed (a : BitVec 64)
    (ha : guestByteArena (holByteAlign a) = true) : guestByteArena a = true := by
  change decide (scratchStart ≤ a.toNat ∧ a.toNat < scratchEnd) = true
  apply decide_eq_true
  have h : scratchStart ≤ (holByteAlign a).toNat ∧
      (holByteAlign a).toNat < scratchEnd := of_decide_eq_true ha
  rw [holByteAlign_toNat (Or.inr rfl)] at h
  norm_num [scratchStart, scratchEnd] at h ⊢
  omega

#print axioms guestByteArena_word_closed

#print axioms guestArena_machine_separation

#print axioms ordinaryDomain_interval
#print axioms guestDomain_union
#print axioms guestArena_below_initialization
#print axioms requested_union_ordinaryDomain
end InitE.Op5
