import InitECandidate.Runtime.HeaderWithdrawalStatement46
import InitECandidate.Runtime.RlpWindowShiftGeneral
import InitECandidate.Runtime.Bn254AccelInitSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The withdrawal slice loop consumes one 64-byte allocation per iteration, so iteration `j` starts
at the concrete heap word `heapBase + 64 * j`. -/
def wdHeapWord (heapBase : BitVec 64) (j : Nat) : BitVec 64 :=
  heapBase + BitVec.ofNat 64 (64 * j)

theorem wdHeapWord_zero (heapBase : BitVec 64) : wdHeapWord heapBase 0 = heapBase := by
  simp [wdHeapWord]

theorem wdHeapWord_toNat (heapBase : BitVec 64) (j : Nat)
    (fit : heapBase.toNat + 64 * j < 2^64) :
    (wdHeapWord heapBase j).toNat = heapBase.toNat + 64 * j := by
  have off : 64 * j < 2^64 := by omega
  rw [wdHeapWord, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt off,
    Nat.mod_eq_of_lt fit]

theorem wdHeapWord_succ (heapBase : BitVec 64) (j : Nat)
    (aligned : heapBase.toNat % 8 = 0)
    (fit : heapBase.toNat + 64 * (j + 1) < 2^64)
    (limit : heapBase.toNat + 64 * (j + 1) ≤ 33806089496) :
    wdHeapWord heapBase (j + 1) = allocationEnd (wdHeapWord heapBase j) 64 := by
  have fitj : heapBase.toNat + 64 * j < 2^64 := by omega
  have toNatj : (wdHeapWord heapBase j).toNat = heapBase.toNat + 64 * j :=
    wdHeapWord_toNat heapBase j fitj
  have alignj : (wdHeapWord heapBase j).toNat % 8 = 0 := by
    rw [toNatj]
    omega
  have sizeNat : (64#64 : BitVec 64).toNat = 64 := by decide
  have endEq : allocationEnd (wdHeapWord heapBase j) 64 = wdHeapWord heapBase j + 64#64 :=
    allocationEnd_aligned_exact (wdHeapWord heapBase j) 64 alignj (by decide) (by
      show (wdHeapWord heapBase j).toNat + (64#64 : BitVec 64).toNat ≤ 33806089496
      rw [toNatj, sizeNat]
      omega)
  rw [endEq, wdHeapWord, wdHeapWord]
  have offSucc : (BitVec.ofNat 64 (64 * (j + 1)) : BitVec 64) =
      BitVec.ofNat 64 (64 * j) + 64#64 := by
    rw [show 64 * (j + 1) = 64 * j + 64 from by omega, BitVec.ofNat_add]
  rw [offSucc, BitVec.add_assoc]

/-- A single out-of-window fact for the whole heap run gives the per-iteration windows. -/
theorem wdHeapWord_out (heapBase w : BitVec 64) (nwd : Nat)
    (out : ¬ MWin heapBase (64 * nwd + 64) w) :
    ∀ j, j ≤ nwd → ¬ MWin (wdHeapWord heapBase j) 64 w := by
  intro j hj win
  have widen : MWin heapBase (64 * j + 64) w := mwin_shift_nat (D := heapBase) (k := 64 * j) (N := 64) win
  exact mwin_mono (by omega) out widen

/-- The per-iteration heap words stay in the 64-bit range while the loop runs. -/
theorem wdHeapWord_bounds (heapBase : BitVec 64) (nwd : Nat)
    (fit : heapBase.toNat + 64 * nwd + 64 < 2^64) :
    ∀ j, j ≤ nwd → (wdHeapWord heapBase j).toNat + 64 < 2^64 := by
  intro j hj
  rw [wdHeapWord_toNat heapBase j (by omega)]
  omega

/-- Statement 46 with the heap chain reduced to concrete, checkable entry facts: the arena is
8-aligned, the whole run stays inside the 64-bit range and the allocator limit, and both watched
cells start outside the concatenation of all the run's allocation windows. -/
theorem payloadHeader46_window_entry {F : Type} (t : PanSemStateFiniteExact 64 F)
    (I0 nwd pl slices heapBase w read X : BitVec 64)
    (readEq : read = pl + 48#64)
    (atCounter : t.locals.lookup (ofString "i") = some (ValueHOL.val (HolWordLab.word I0)))
    (atNwd : t.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)))
    (atPl : t.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (freshE : t.locals.lookup (ofString "e") = none)
    (atSlices : t.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word slices)))
    (atHeap : t.globals.lookup (ofString "heap_ptr") = some (ValueHOL.val (HolWordLab.word heapBase)))
    (code : t.code = originalRuntimeCode)
    (aligned : heapBase.toNat % 8 = 0)
    (fitRange : heapBase.toNat + 64 * nwd.toNat + 128 < 2^64)
    (limit : heapBase.toNat + 64 * nwd.toNat + 64 ≤ 33806089496)
    (initialLe : I0.toNat ≤ nwd.toNat)
    (smallNwd : nwd.toNat < 2^63)
    (outW : ¬ MWin heapBase (64 * nwd.toNat + 64) w)
    (outR : ¬ MWin heapBase (64 * nwd.toNat + 64) read)
    (addrRead : t.memaddrs read)
    (sliceW : ∀ j, j ≤ nwd.toNat →
      w ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 ∧
      w ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 + 8#64)
    (sliceR : ∀ j, j ≤ nwd.toNat →
      read ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 ∧
      read ≠ slices + (I0 + BitVec.ofNat 64 j) * 16#64 + 8#64)
    (memRead : t.memory read = HolWordLab.word X)
    (tail : (evaluateHOLFiniteState (evaluateHOLFiniteState t wdSliceLoop).2
        (actualPayloadHeaderAt 47)).2.memory w = (evaluateHOLFiniteState t wdSliceLoop).2.memory w) :
    (evaluateHOLFiniteState t (actualPayloadHeaderAt 46)).2.memory w = t.memory w := by
  have fitNat : heapBase.toNat + 64 * nwd.toNat + 64 < 2^64 := by omega
  refine payloadHeader46_window t I0 nwd pl slices heapBase w read X (wdHeapWord heapBase) readEq
    atCounter atNwd atPl freshE atSlices (by simpa [wdHeapWord_zero] using atHeap) code
    (wdHeapWord_zero heapBase) ?_ initialLe smallNwd
    (wdHeapWord_bounds heapBase nwd.toNat (by omega))
    (wdHeapWord_out heapBase w nwd.toNat outW)
    (wdHeapWord_out heapBase read nwd.toNat outR)
    addrRead sliceW sliceR memRead tail
  intro j hj
  exact wdHeapWord_succ heapBase j aligned (by omega) (by omega)

#print axioms payloadHeader46_window_entry
#print axioms wdHeapWord_succ
#print axioms wdHeapWord_out
#print axioms wdHeapWord_bounds
end InitECandidate.Runtime
