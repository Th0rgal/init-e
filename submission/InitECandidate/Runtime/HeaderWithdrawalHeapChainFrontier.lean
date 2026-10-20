import InitECandidate.Runtime.HeaderWithdrawalHeapChain
import InitECandidate.Runtime.HeaderWithdrawalStatement46
import InitECandidate.Runtime.HeaderWithdrawalEntryGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Adding a multiple of 64 preserves 8-alignment of the arithmetic heap chain. -/
theorem wdHeapWord_aligned (heapBase : BitVec 64) (j : Nat) (al : heapBase.toNat % 8 = 0) :
    (wdHeapWord heapBase j).toNat % 8 = 0 := by
  have offVal : (BitVec.ofNat 64 (64 * j)).toNat % 8 = 0 := by
    rw [BitVec.toNat_ofNat]; omega
  have key : 2^64 = 8 * 2^61 := by decide
  rw [wdHeapWord, BitVec.toNat_add, key, Nat.mod_mul_right_mod]
  omega

/-- The heap chain step driven by arithmetic facts only: no allocator-room cap, just the frontier's
8-alignment and the 64-bit range at this step. -/
theorem wdHeapWord_step_frontier (heapBase : BitVec 64) (j : Nat)
    (al : heapBase.toNat % 8 = 0)
    (heapFit : heapBase.toNat + 64 * j < 2^64)
    (nextFit : heapBase.toNat + 64 * j + 71 < 2^64) :
    wdHeapWord heapBase (j + 1) = allocationEnd (wdHeapWord heapBase j) 64 := by
  have jVal : (wdHeapWord heapBase j).toNat = heapBase.toNat + 64 * j :=
    wdHeapWord_toNat heapBase j heapFit
  have nextVal : (wdHeapWord heapBase (j + 1)).toNat = heapBase.toNat + 64 * (j + 1) :=
    wdHeapWord_toNat heapBase (j + 1) (by omega)
  have stepAligned : (wdHeapWord heapBase j).toNat % 8 = 0 := wdHeapWord_aligned heapBase j al
  have stepNowrap : (wdHeapWord heapBase j).toNat + 71 < 2^64 := by rw [jVal]; omega
  have step := wd_heap_step_no_cap (wdHeapWord heapBase j) stepAligned stepNowrap
  rw [step]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, nextVal, jVal]
  have s64 : (64#64 : BitVec 64).toNat = 64 := by decide
  rw [s64]
  omega

/-- Statement 46's window with the arithmetic heap chain and **no** allocator-room cap: the per-step
facts are only the frontier's 8-alignment and the 64-bit range at each step, and both watched words lie
below the slice array. -/
theorem payloadHeader46_window_frontier {F : Type} (t : PanSemStateFiniteExact 64 F)
    (nwd pl slices heapBase w read X : BitVec 64)
    (readEq : read = pl + 48#64)
    (atCounter : t.locals.lookup (ofString "i") = some (ValueHOL.val (HolWordLab.word 0#64)))
    (atNwd : t.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)))
    (atPl : t.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (freshE : t.locals.lookup (ofString "e") = none)
    (atSlices : t.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word slices)))
    (atHeap : t.globals.lookup (ofString "heap_ptr") = some (ValueHOL.val (HolWordLab.word heapBase)))
    (code : t.code = originalRuntimeCode)
    (aligned : heapBase.toNat % 8 = 0)
    (fitAll : ∀ j, j ≤ nwd.toNat → heapBase.toNat + 64 * j + 71 < 2^64)
    (smallNwd : nwd.toNat < 2^63)
    (slicesAbove : slices.toNat ≤ heapBase.toNat)
    (belowRead : read.toNat < slices.toNat)
    (belowW : w.toNat < slices.toNat)
    (noWrapCells : slices.toNat + 16 * nwd.toNat + 8 < 2^64)
    (addrRead : t.memaddrs read)
    (memRead : t.memory read = HolWordLab.word X)
    (tail : (evaluateHOLFiniteState (evaluateHOLFiniteState t wdSliceLoop).2
        (actualPayloadHeaderAt 47)).2.memory w = (evaluateHOLFiniteState t wdSliceLoop).2.memory w) :
    (evaluateHOLFiniteState t (actualPayloadHeaderAt 46)).2.memory w = t.memory w := by
  refine payloadHeader46_window t 0#64 nwd pl slices heapBase w read X
    (fun j => wdHeapWord heapBase j) readEq (by simpa using atCounter) atNwd atPl freshE atSlices
    atHeap code (wdHeapWord_zero heapBase) ?_ ?_ smallNwd ?_ ?_ ?_ addrRead ?_ ?_ memRead tail
  · intro j hj
    exact wdHeapWord_step_frontier heapBase j aligned (by have := fitAll j hj; omega)
      (fitAll j hj)
  · simpa using (show (0#64 : BitVec 64).toNat = 0 from rfl)
  · intro j hj
    have jVal : (wdHeapWord heapBase j).toNat = heapBase.toNat + 64 * j :=
      wdHeapWord_toNat heapBase j (by have := fitAll j hj; omega)
    have := fitAll j hj
    omega
  · intro j hj
    have jVal : (wdHeapWord heapBase j).toNat = heapBase.toNat + 64 * j :=
      wdHeapWord_toNat heapBase j (by have := fitAll j hj; omega)
    have fit := fitAll j hj
    have baseLe : heapBase.toNat ≤ (wdHeapWord heapBase j).toNat := by rw [jVal]; omega
    exact mwin_above (D := wdHeapWord heapBase j) (N := 64) (by omega)
      (wdHeapWord_aligned heapBase j aligned) (by omega)
  · intro j hj
    have jVal : (wdHeapWord heapBase j).toNat = heapBase.toNat + 64 * j :=
      wdHeapWord_toNat heapBase j (by have := fitAll j hj; omega)
    have fit := fitAll j hj
    have baseLe : heapBase.toNat ≤ (wdHeapWord heapBase j).toNat := by rw [jVal]; omega
    exact mwin_above (D := wdHeapWord heapBase j) (N := 64) (by omega)
      (wdHeapWord_aligned heapBase j aligned) (by omega)
  · intro j hj
    have cells := wd_slice_cells_below w slices nwd.toNat j (by omega) noWrapCells hj
    simpa [BitVec.zero_add] using cells
  · intro j hj
    have cells := wd_slice_cells_below read slices nwd.toNat j (by omega) noWrapCells hj
    simpa [BitVec.zero_add] using cells

#print axioms payloadHeader46_window_frontier
#print axioms wdHeapWord_aligned
#print axioms wdHeapWord_step_frontier
end InitECandidate.Runtime
