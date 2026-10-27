import InitE.Parameters
import Flapjack.Misc.Alignment
import Mathlib.Tactic

/-! Region algebra for Op 5. Endpoints are byte addresses; domains contain
aligned word-cell starts. The persistent region excludes globals and stack.
This module deliberately does not change the fixed challenge semantics. -/
namespace InitE.Op5

/-- A half-open byte interval, without modular endpoint arithmetic. -/
def region (lo hi : Nat) (a : BitVec 64) : Prop := lo ≤ a.toNat ∧ a.toNat < hi

/-- Disjoint scratch plus persistent storage, with explicit alignment. -/
def twoRegion (scratchLo scratchHi persistentLo persistentHi : Nat)
    (a : BitVec 64) : Prop :=
  a.toNat % 8 = 0 ∧ (region scratchLo scratchHi a ∨ region persistentLo persistentHi a)

instance (sl sh pl ph : Nat) : DecidablePred (twoRegion sl sh pl ph) :=
  fun a => by
    unfold twoRegion region
    infer_instance

theorem regions_disjoint (sl sh pl ph : Nat) (h : sh ≤ pl) (a : BitVec 64) :
    ¬ (region sl sh a ∧ region pl ph a) := by
  unfold region
  omega

theorem twoRegion_below_stack (sl sh pl ph stackLo stackHi : Nat)
    (hs : sh ≤ stackLo) (hp : ph ≤ stackLo) (a : BitVec 64)
    (ha : twoRegion sl sh pl ph a) : ¬ region stackLo stackHi a := by
  simp only [twoRegion, region] at ha ⊢
  omega

/-- Writes confined to the machine stack preserve every source word in both regions. -/
theorem stack_write_frame {V : Type} (sl sh pl ph stackLo stackHi : Nat)
    (hs : sh ≤ stackLo) (hp : ph ≤ stackLo)
    (before after : BitVec 64 → V)
    (writes : ∀ a, ¬ region stackLo stackHi a → after a = before a) :
    ∀ a, twoRegion sl sh pl ph a → after a = before a := by
  intro a ha
  exact writes a (twoRegion_below_stack sl sh pl ph stackLo stackHi hs hp a ha)

/-- The executable guest's below-base scratch layout in the pinned revision. -/
def guestDomain := twoRegion scratchStart scratchEnd sourceBase heapEnd

/-- The requested arena and disjoint persistent bump region in the operation brief. -/
def requestedDomain := twoRegion 0xa1001000 0xa1c00000 0xa1c00000 heapEnd

theorem guest_scratch_persistent_disjoint (a : BitVec 64) :
    ¬ (region scratchStart scratchEnd a ∧ region sourceBase heapEnd a) :=
  regions_disjoint _ _ _ _ (by decide) a

theorem guest_stack_disjoint (a : BitVec 64) (ha : guestDomain a) :
    ¬ region stackStart ramEnd a :=
  twoRegion_below_stack _ _ _ _ _ _ (by decide) (by decide) a ha

theorem requested_stack_disjoint (a : BitVec 64) (ha : requestedDomain a) :
    ¬ region stackStart ramEnd a :=
  twoRegion_below_stack _ _ _ _ _ _ (by decide) (by decide) a ha

/-- At this revision the requested scratch region is above sourceBase. -/
theorem requested_scratch_already_above_base (a : BitVec 64)
    (ha : region 0xa1001000 0xa1c00000 a) : region sourceBase heapEnd a := by
  unfold region at ha ⊢
  norm_num [sourceBase, heapEnd, stackStart, ramEnd, ramStart, ramSize,
    stackSize, globalsWords]
  omega

#print axioms stack_write_frame
#print axioms guest_stack_disjoint
#print axioms requested_stack_disjoint
end InitE.Op5
