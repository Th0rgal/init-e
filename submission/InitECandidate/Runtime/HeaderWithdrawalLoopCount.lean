import InitECandidate.Runtime.HeaderWithdrawalLoopFence
import InitECandidate.Runtime.HeaderWithdrawalLoopBody
import InitECandidate.Runtime.HeaderWithdrawalLoopWhile
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- The statement-46 loop invariant: the counter is the entry index plus the number of completed
iterations, the heap pointer is the matching frontier word `H k`, the memory domain is the entry
domain `m`, and the watched `pl + 48` cell still holds the entry value. -/
def WdLoopInv (m : BitVec 64 → Prop) (I0 nwd pl slices read X : BitVec 64) (H : Nat → BitVec 64)
    {F : Type} (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ k : Nat, I0.toNat + k ≤ nwd.toNat ∧
    (∀ a, t.memaddrs a ↔ m a) ∧
    t.locals.lookup (ofString "i") =
      some (ValueHOL.val (HolWordLab.word (I0 + BitVec.ofNat 64 k))) ∧
    t.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)) ∧
    t.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)) ∧
    t.locals.lookup (ofString "e") = none ∧
    t.globals.lookup (ofString "wd_rlp_slices") = some (ValueHOL.val (HolWordLab.word slices)) ∧
    t.globals.lookup (ofString "heap_ptr") = some (ValueHOL.val (HolWordLab.word (H k))) ∧
    t.code = originalRuntimeCode ∧
    m read ∧
    t.memory read = HolWordLab.word X

/-- The heap pointer value and its cap come from the frontier hypothesis. -/
theorem wdLoopInv_heapOf (m : BitVec 64 → Prop) (I0 nwd pl slices read X : BitVec 64)
    (H : Nat → BitVec 64) (frontier : ∀ k, k ≤ nwd.toNat → (H k).toNat ≤ 33806089496) :
    ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), WdLoopInv m I0 nwd pl slices read X H t →
      ∃ heap : BitVec 64, t.globals.lookup (ofString "heap_ptr") =
        some (ValueHOL.val (HolWordLab.word heap)) ∧ heap.toNat ≤ 33806089496 := by
  intro F t inv
  obtain ⟨k, bound, dom, atI, atNwd, atPl, freshE, atSlices, atHeap, codeEq, watched, cell⟩ := inv
  exact ⟨H k, atHeap, frontier k (by omega)⟩

/-- The fence is the entry memory domain's fence. -/
theorem wdLoopInv_fence (m : BitVec 64 → Prop) (I0 nwd pl slices read X : BitVec 64)
    (H : Nat → BitVec 64) {DF : Nat} (fence : Fence m DF) :
    ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), WdLoopInv m I0 nwd pl slices read X H t →
      Fence t.memaddrs DF := by
  intro F t inv
  obtain ⟨k, bound, dom, atI, atNwd, atPl, freshE, atSlices, atHeap, codeEq, watched, cell⟩ := inv
  intro a ha
  exact fence a ((dom a).mp ha)

/-- The loop bound `nwd` is read from the invariant. -/
theorem wdLoopInv_atBound (m : BitVec 64 → Prop) (I0 nwd pl slices read X : BitVec 64)
    (H : Nat → BitVec 64) :
    ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), WdLoopInv m I0 nwd pl slices read X H t →
      t.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)) := by
  intro F t inv
  obtain ⟨k, bound, dom, atI, atNwd, atPl, freshE, atSlices, atHeap, codeEq, watched, cell⟩ := inv
  exact atNwd

/-- One iteration never continues. -/
theorem wdLoopInv_noContinue (m : BitVec 64 → Prop) (I0 nwd pl slices read X : BitVec 64)
    (H : Nat → BitVec 64) :
    ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      WdLoopInv m I0 nwd pl slices read X H t →
      (evaluateHOLFiniteState t wdSliceLoopBody).1 ≠ some .continue := by
  intro F t w _
  exact (wdSliceLoopBody_noControl t).1

/-- The invariant is preserved by the loop's clock decrement. -/
theorem wdLoopInv_decrease (m : BitVec 64 → Prop) (I0 nwd pl slices read X : BitVec 64)
    (H : Nat → BitVec 64) :
    ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), WdLoopInv m I0 nwd pl slices read X H t →
      WdLoopInv m I0 nwd pl slices read X H (decClockHOLFinite t) := by
  intro F t inv
  obtain ⟨k, bound, dom, atI, atNwd, atPl, freshE, atSlices, atHeap, codeEq, watched, cell⟩ := inv
  exact ⟨k, bound, by simpa [decClockHOLFinite] using dom,
    by simpa [decClockHOLFinite] using atI, by simpa [decClockHOLFinite] using atNwd,
    by simpa [decClockHOLFinite] using atPl, by simpa [decClockHOLFinite] using freshE,
    by simpa [decClockHOLFinite] using atSlices, by simpa [decClockHOLFinite] using atHeap,
    by simpa [decClockHOLFinite] using codeEq, watched, by simpa [decClockHOLFinite] using cell⟩

/-- The evaluated encoder argument at every invariant state, from the watched `pl + 48` cell. -/
theorem wdLoopInv_argsOf (m : BitVec 64 → Prop) (I0 nwd pl slices read X : BitVec 64)
    (H : Nat → BitVec 64) (readEq : read = pl + 48#64) :
    ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), WdLoopInv m I0 nwd pl slices read X H t →
      ∃ argumentWord : BitVec 64,
        evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
            .panop .mul [.var .local (ofString "i"), .const (44#64)]]] =
          some [ValueHOL.val (HolWordLab.word argumentWord)] := by
  intro F t inv
  obtain ⟨k, bound, dom, atI, atNwd, atPl, freshE, atSlices, atHeap, codeEq, watched, cell⟩ := inv
  have addrOk : t.memaddrs (pl + 48#64) := by
    rw [← readEq]
    exact (dom read).mpr watched
  have mem : t.memory (pl + 48#64) = HolWordLab.word X := by
    rw [← readEq]
    exact cell
  exact ⟨X + (I0 + BitVec.ofNat 64 k) * 44#64,
    wd_slice_args t I0 pl X k atPl atI addrOk mem⟩


/-- The counter word after `k` iterations is the entry index plus `k`. -/
theorem wdLoopInv_counter_toNat {I0 : BitVec 64} {k : Nat} (hk : k < 2 ^ 64)
    (hsmall : I0.toNat + k < 2 ^ 64) : (I0 + BitVec.ofNat 64 k).toNat = I0.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hsmall]

/-- The successor counter word of `k` completed iterations is the one of `k + 1`. -/
theorem wdLoopInv_counter_succ {I0 : BitVec 64} {k : Nat} (hk : k + 1 < 2 ^ 64) :
    (I0 + BitVec.ofNat 64 k) + 1#64 = I0 + BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk]

/-- **Counter advance** of one statement-46 iteration, from the invariant. -/
theorem wdLoopInv_advance (m : BitVec 64 → Prop) (I0 nwd pl slices read X : BitVec 64)
    (H : Nat → BitVec 64) (readEq : read = pl + 48#64) :
    ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      WdLoopInv m I0 nwd pl slices read X H t →
      t.locals.lookup (ofString "i") = some (ValueHOL.val (HolWordLab.word w)) →
      (evaluateHOLFiniteState t wdSliceLoopBody).1 = none →
      (evaluateHOLFiniteState t wdSliceLoopBody).2.locals.lookup (ofString "i") =
        some (ValueHOL.val (HolWordLab.word (w + 1#64))) ∧
      (evaluateHOLFiniteState t wdSliceLoopBody).2.code = t.code := by
  intro F t w inv atCounter normal
  obtain ⟨k, bound, dom, atI, atNwd, atPl, freshE, atSlices, atHeap, codeEq, watched, cell⟩ := inv
  have hsome : some (ValueHOL.val (HolWordLab.word w)) =
      some (ValueHOL.val (HolWordLab.word (I0 + BitVec.ofNat 64 k))) := by
    rw [← atCounter, atI]
  have hw : w = I0 + BitVec.ofNat 64 k := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj hsome))
  have addrOk : t.memaddrs (pl + 48#64) := by
    rw [← readEq]
    exact (dom read).mpr watched
  have mem : t.memory (pl + 48#64) = HolWordLab.word X := by
    rw [← readEq]
    exact cell
  have hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
        .panop .mul [.var .local (ofString "i"), .const (44#64)]]] =
      some [ValueHOL.val (HolWordLab.word (X + (I0 + BitVec.ofNat 64 k) * 44#64))] :=
    wd_slice_args t I0 pl X k atPl atI addrOk mem
  obtain ⟨argumentWord, hargsWord⟩ := wdLoopInv_argsOf m I0 nwd pl slices read X H readEq t
    ⟨k, bound, dom, atI, atNwd, atPl, freshE, atSlices, atHeap, codeEq, watched, cell⟩
  have codeEq' : t.code = originalRuntimeCode := codeEq
  obtain ⟨first, second, st, bodyRun, shapeOk⟩ := wd_slice_step_outcome t argumentWord codeEq' hargsWord normal
  obtain ⟨succI, succNwd, succPl, succE, succSlices, succHeap⟩ :=
    wd_slice_step_successor t (I0 + BitVec.ofNat 64 k) nwd pl slices (H k) argumentWord first second st
      atI atNwd atPl freshE atSlices atHeap codeEq' hargsWord bodyRun shapeOk normal
  refine ⟨?_, ?_⟩
  · rw [succI, hw]
  · exact (evaluateHOLFiniteState_metadata t wdSliceLoopBody).1


/-- **Invariant preservation** of one statement-46 iteration: the counter advances by one, the heap
pointer advances to `H (k+1) = allocationEnd (H k) 64`, the memory domain and the watched `pl + 48`
cell are unchanged, and the remaining bindings are untouched. -/
theorem wdLoopInv_keep (m : BitVec 64 → Prop) (I0 nwd pl slices read X : BitVec 64)
    (H : Nat → BitVec 64) (readEq : read = pl + 48#64)
    (frontier : ∀ k, k ≤ nwd.toNat → (H k).toNat ≤ 33806089496)
    (outRead : ∀ k, ¬ MWin (H k) 64 read)
    (sliceRead : ∀ c : BitVec 64,
      read ≠ slices + c * 16#64 ∧ read ≠ slices + (c * 16#64 + 8#64))
    (heapStep : ∀ k, k ≤ nwd.toNat → H (k + 1) = allocationEnd (H k) 64) :
    ∀ {F : Type} (t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      WdLoopInv m I0 nwd pl slices read X H t →
      t.code = originalRuntimeCode →
      t.locals.lookup (ofString "i") = some (ValueHOL.val (HolWordLab.word w)) →
      w.toNat < nwd.toNat →
      (evaluateHOLFiniteState t wdSliceLoopBody).1 = none →
      WdLoopInv m I0 nwd pl slices read X H (evaluateHOLFiniteState t wdSliceLoopBody).2 := by
  intro F t w inv code atCounter lt normal
  obtain ⟨k, bound, dom, atI, atNwd, atPl, freshE, atSlices, atHeap, codeEq, watched, cell⟩ := inv
  have addrOk : t.memaddrs (pl + 48#64) := by
    rw [← readEq]
    exact (dom read).mpr watched
  have mem : t.memory (pl + 48#64) = HolWordLab.word X := by
    rw [← readEq]
    exact cell
  have hargs := wd_slice_args t I0 pl X k atPl atI addrOk mem
  obtain ⟨first, second, st, bodyRun, shapeOk⟩ :=
    wd_slice_step_outcome t (X + (I0 + BitVec.ofNat 64 k) * 44#64) codeEq hargs normal
  obtain ⟨succI, succNwd, succPl, succE, succSlices, succHeap⟩ :=
    wd_slice_step_successor t (I0 + BitVec.ofNat 64 k) nwd pl slices (H k) (X + (I0 + BitVec.ofNat 64 k) * 44#64)
      first second st atI atNwd atPl freshE atSlices atHeap codeEq hargs bodyRun shapeOk normal
  have hklt : k ≤ nwd.toNat := by omega
  have heapBound : (H k).toNat + 64 < 2 ^ 64 := by
    have := frontier k hklt
    omega
  have window := wd_slice_step_window t slices (I0 + BitVec.ofNat 64 k)
    (X + (I0 + BitVec.ofNat 64 k) * 44#64) (H k) read atI atSlices atHeap codeEq heapBound
    (outRead k) (sliceRead _).1 (sliceRead _).2 hargs
  have hno : (I0 + BitVec.ofNat 64 k).toNat = I0.toNat + k :=
    wdLoopInv_counter_toNat (by omega) (by omega)
  have hw : I0 + BitVec.ofNat 64 k = w := by
    have hsome : some (ValueHOL.val (HolWordLab.word (I0 + BitVec.ofNat 64 k))) =
        some (ValueHOL.val (HolWordLab.word w)) := by
      rw [← atI, atCounter]
    exact (HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj hsome))).symm ▸ rfl
  have ltCounter : (I0 + BitVec.ofNat 64 k).toNat < nwd.toNat := by
    rw [hw]
    exact lt
  have ltNat : I0.toNat + k < nwd.toNat := by
    rw [← hno]
    exact ltCounter
  have succCounter : (evaluateHOLFiniteState t wdSliceLoopBody).2.locals.lookup (ofString "i") =
      some (ValueHOL.val (HolWordLab.word (I0 + BitVec.ofNat 64 (k + 1)))) := by
    rw [succI, wdLoopInv_counter_succ (by omega)]
  refine ⟨k + 1, by omega, ?_, succCounter, succNwd, succPl, succE, succSlices, ?_, ?_, watched, ?_⟩
  · simpa [(evaluateHOLFiniteState_metadata t wdSliceLoopBody).2.1] using dom
  · rw [succHeap, heapStep k hklt]
  · exact (evaluateHOLFiniteState_metadata t wdSliceLoopBody).1.trans code
  · rw [window]
    exact cell


/-- **Statement-46 loop runtime bound, fully discharged.** With the concrete invariant in place —
heap frontier `H`, watched `pl + 48` cell, memory domain `m`, code, and the counter — the slice loop
`while i < nwd` of `actualPayloadHeaderAt 46` satisfies, for every outcome,
`clock ≤ post.clock + (nwd.toNat - I0.toNat) * (encodeWithdrawalSourceCost DF + 2)` with
`post.clock ≤ clock` and no timeout, where each iteration's cost is the *installed* withdrawal
encoder's source cost plus the condition tick and the two slice stores. No future-runtime, callee,
frame or fuel oracle is used. -/
theorem wdSliceLoop_count (DF : Nat) (m : BitVec 64 → Prop) (I0 nwd pl slices read X : BitVec 64)
    (H : Nat → BitVec 64) (readEq : read = pl + 48#64) (fence : Fence m DF)
    (smallDF : DF + 8 ≤ 2 ^ 62) (bigDF : 33806089496 ≤ DF)
    (frontier : ∀ k, k ≤ nwd.toNat → (H k).toNat ≤ 33806089496)
    (outRead : ∀ k, ¬ MWin (H k) 64 read)
    (sliceRead : ∀ c : BitVec 64,
      read ≠ slices + c * 16#64 ∧ read ≠ slices + (c * 16#64 + 8#64))
    (heapStep : ∀ k, k ≤ nwd.toNat → H (k + 1) = allocationEnd (H k) 64)
    (small : nwd.toNat + 1 < 2 ^ 63) :
    ∀ {F : Type} (t : PanSemStateFiniteExact 64 F), WdLoopInv m I0 nwd pl slices read X H t →
      t.code = originalRuntimeCode →
      t.locals.lookup (ofString "i") = some (ValueHOL.val (HolWordLab.word I0)) →
      I0.toNat ≤ nwd.toNat →
      (nwd.toNat - I0.toNat) * ((encodeWithdrawalSourceCost DF + 1) + 1) ≤ t.clock →
      t.clock ≤ (evaluateHOLFiniteState t wdSliceLoop).2.clock +
          (nwd.toNat - I0.toNat) * ((encodeWithdrawalSourceCost DF + 1) + 1) ∧
        (evaluateHOLFiniteState t wdSliceLoop).2.clock ≤ t.clock ∧
        (evaluateHOLFiniteState t wdSliceLoop).1 ≠ some .timeOut := by
  intro F t entry code atCounter le budget
  exact wdSliceLoop_runBounded_of_invariant DF nwd (WdLoopInv m I0 nwd pl slices read X H)
    (wdLoopInv_heapOf m I0 nwd pl slices read X H frontier)
    (wdLoopInv_fence m I0 nwd pl slices read X H fence)
    (wdLoopInv_argsOf m I0 nwd pl slices read X H readEq)
    smallDF bigDF
    (wdLoopInv_keep m I0 nwd pl slices read X H readEq frontier outRead sliceRead heapStep)
    (wdLoopInv_advance m I0 nwd pl slices read X H readEq)
    (wdLoopInv_noContinue m I0 nwd pl slices read X H)
    (wdLoopInv_decrease m I0 nwd pl slices read X H)
    (wdLoopInv_atBound m I0 nwd pl slices read X H)
    small (nwd.toNat - I0.toNat) t entry code I0 atCounter (by omega) rfl budget

#print axioms wdSliceLoop_count
#print axioms wdLoopInv_keep
#print axioms wdLoopInv_advance
#print axioms wdLoopInv_heapOf
#print axioms wdLoopInv_fence
#print axioms wdLoopInv_atBound
#print axioms wdLoopInv_noContinue
#print axioms wdLoopInv_decrease
#print axioms wdLoopInv_argsOf
end InitECandidate.Runtime
