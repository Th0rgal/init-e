import InitECandidate.Runtime.HeaderWithdrawalLoopCount
import InitECandidate.Runtime.HeaderWithdrawalEntryGeometry
import InitECandidate.Runtime.HeaderWithdrawalEntryFacts
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- The concrete heap chain of the loop stays inside the allocator limit. -/
theorem wdHeapWord_frontier (loopHeap : BitVec 64) (nwd : Nat)
    (limit : loopHeap.toNat + 64 * nwd ≤ 33806089496) :
    ∀ j, j ≤ nwd → (wdHeapWord loopHeap j).toNat ≤ 33806089496 := by
  intro j hj
  rw [wdHeapWord_toNat loopHeap j (by omega)]
  omega

/-- **Statement 46 at its actual entry state.** The entry state is the one statement 44's allocator
call produces: `wd_rlp_slices` and `heap_ptr` both start at the arena base, the counter is the
statement-45 declaration `0`, and the payload pointer, memory domain and code are inherited. All
per-iteration obligations of `wdSliceLoop_count` — the heap frontier, the per-iteration windows above
both watched cells, and the slice-cell separation — are discharged here from the source allocation and
count facts (`wdHeapWord_*`, `wd_heap_window_below`, `wd_slice_cells_below`), leaving only the
ambient fence and the fuel budget. -/
theorem wdSliceLoop_count_entry (DF : Nat) {F : Type} (t : PanSemStateFiniteExact 64 F)
    (nwd pl slices loopHeap read X : BitVec 64)
    (readEq : read = pl + 48#64)
    (al : loopHeap.toNat % 8 = 0)
    (fit : loopHeap.toNat + 64 * nwd.toNat + 64 < 2 ^ 64)
    (limit : loopHeap.toNat + 64 * nwd.toNat + 64 ≤ 33806089496)
    (smallNwd : nwd.toNat + 1 < 2 ^ 63)
    (slicesBelow : slices.toNat ≤ loopHeap.toNat)
    (readBelow : read.toNat < slices.toNat)
    (noWrapCells : slices.toNat + 16 * nwd.toNat + 8 < 2 ^ 64)
    (fence : Fence t.memaddrs DF) (smallDF : DF + 8 ≤ 2 ^ 62) (bigDF : 33806089496 ≤ DF)
    (atCounter : t.locals.lookup (ofString "i") =
      some (ValueHOL.val (HolWordLab.word 0#64)))
    (atNwd : t.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)))
    (atPl : t.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (freshE : t.locals.lookup (ofString "e") = none)
    (atSlices : t.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word slices)))
    (atHeap : t.globals.lookup (ofString "heap_ptr") =
      some (ValueHOL.val (HolWordLab.word loopHeap)))
    (code : t.code = originalRuntimeCode)
    (addrRead : t.memaddrs read) (memRead : t.memory read = HolWordLab.word X)
    (budget : nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1) ≤ t.clock) :
    t.clock ≤ (evaluateHOLFiniteState t wdSliceLoop).2.clock +
        nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1) ∧
      (evaluateHOLFiniteState t wdSliceLoop).2.clock ≤ t.clock ∧
      (evaluateHOLFiniteState t wdSliceLoop).1 ≠ some .timeOut := by
  have entry : WdLoopInv t.memaddrs 0#64 nwd pl slices read X (wdHeapWord loopHeap) t :=
    ⟨0, by simp, fun a => Iff.rfl, by simpa using atCounter, atNwd, atPl, freshE, atSlices,
      by simpa [wdHeapWord_zero] using atHeap, code, addrRead, memRead,
      by simpa [wdHeapWord_zero] using
        (wdHeapWord_frontier loopHeap nwd.toNat (by omega) 0 (by omega))⟩
  have frontier : ∀ j, j ≤ nwd.toNat + 1 → (wdHeapWord loopHeap j).toNat ≤ 33806089496 :=
    wdHeapWord_frontier loopHeap (nwd.toNat + 1) (by omega)
  have outRead : ∀ j, j ≤ nwd.toNat → ¬ MWin (wdHeapWord loopHeap j) 64 read :=
    wd_heap_window_below loopHeap read nwd.toNat al (by omega) (by omega)
  have sliceRead : ∀ j, j ≤ nwd.toNat →
      read ≠ slices + (0#64 + BitVec.ofNat 64 j) * 16#64 ∧
      read ≠ slices + ((0#64 + BitVec.ofNat 64 j) * 16#64 + 8#64) := by
    intro j hj
    have cells := wd_slice_cells_below read slices nwd.toNat j (by omega) noWrapCells hj
    simpa [BitVec.add_assoc] using cells
  have heapStep : ∀ j, j ≤ nwd.toNat →
      wdHeapWord loopHeap (j + 1) = allocationEnd (wdHeapWord loopHeap j) 64 := by
    intro j hj
    exact wdHeapWord_succ loopHeap j al (by omega) (by omega)
  have main := wdSliceLoop_count DF t.memaddrs 0#64 nwd pl slices read X (wdHeapWord loopHeap)
    readEq fence smallDF bigDF frontier outRead sliceRead heapStep
    (wdLoopInv_capStep t.memaddrs 0#64 nwd pl slices read X (wdHeapWord loopHeap) frontier heapStep)
    smallNwd
    t entry code (by simpa using atCounter) (by simp) (by simpa using budget)
  exact main


/-- **Statements 44 → 45 → 46 composed at the clock level.** From the pre-allocation header state, the
actual statement-44 allocator call costs one tick and yields the loop arena; statement 45's counter
declaration is free; and then statement 46's loop costs at most
`nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)` ticks. So the pre-allocation clock is bounded by
`1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)` plus the post-loop clock, with no timeout.
The arena facts (`slices` at the arena base, `heap_ptr` at the exact 8-aligned end, the per-iteration
windows and the slice cells above the payload area) are all taken from the source allocation facts. -/
theorem wdSliceLoop_count_alloc (DF : Nat) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (nwd size heapBase oldSlices pl read X : BitVec 64)
    (sizeVal : size = nwd * 16#64 + 16#64)
    (readEq : read = pl + 48#64)
    (atNwd : state.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)))
    (atGlobal : state.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word oldSlices)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") =
      some (ValueHOL.val (HolWordLab.word heapBase)))
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.op .add [(.panop .mul [.var .local (ofString "nwd"), .const (16#64)]),
        .const (16#64)]] = some [.val (.word size)])
    (al : heapBase.toNat % 8 = 0) (sizeAl : size.toNat % 8 = 0)
    (bounded : heapBase.toNat + size.toNat ≤ 33806089496)
    (fit : (allocationEnd heapBase size).toNat + 64 * nwd.toNat + 64 < 2 ^ 64)
    (limit : (allocationEnd heapBase size).toNat + 64 * nwd.toNat + 64 ≤ 33806089496)
    (smallNwd : nwd.toNat + 1 < 2 ^ 63)
    (readBelow : read.toNat < heapBase.toNat)
    (noWrapCells : heapBase.toNat + 16 * nwd.toNat + 8 < 2 ^ 64)
    (fence : Fence state.memaddrs DF) (smallDF : DF + 8 ≤ 2 ^ 62) (bigDF : 33806089496 ≤ DF)
    (atPl : state.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (freshE : state.locals.lookup (ofString "e") = none)
    (addrRead : state.memaddrs read) (memRead : state.memory read = HolWordLab.word X)
    (budget : nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1) + 1 ≤ state.clock) :
    ∃ ready, evaluateHOLFiniteState state (.call
        (some ((some (.global,ofString "wd_rlp_slices")),none)) (ofString "alloc")
        [.op .add [(.panop .mul [.var .local (ofString "nwd"), .const (16#64)]),
          .const (16#64)]]) = (none, ready) ∧
      state.clock ≤ (evaluateHOLFiniteState
          (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready)
          wdSliceLoop).2.clock +
        1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1) ∧
      (evaluateHOLFiniteState
          (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready)
          wdSliceLoop).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState
          (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready)
          wdSliceLoop).1 ≠ some .timeOut := by
  obtain ⟨ready, run, memory, domain, locals, postCode, wdSlices, heapPtr, endToNat, endAligned⟩ :=
    wd_slices_alloc_entry state nwd size heapBase oldSlices sizeVal atNwd atGlobal atHeap code clock args
      al sizeAl bounded
  let ready' : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready
  have readyClock : ready.clock = state.clock - 1 := by
    obtain ⟨ready2, run2, clocks, _⟩ :=
      evaluate_alloc_global_call state _ heapBase size oldSlices (ofString "wd_rlp_slices") args
        code clock atHeap atGlobal (by decide)
        (allocationGuard_of_sum_bound heapBase size bounded) (by rw [endToNat]; omega)
    rw [run] at run2
    injection run2 with _ hstate
    rw [← hstate] at clocks
    exact clocks
  have clockEq : ready'.clock = ready.clock := by simp [ready', setVarHOLFinite]
  have gEq : ready'.globals = ready.globals := by simp [ready', setVarHOLFinite]
  have mEq : ready'.memory = ready.memory := by simp [ready', setVarHOLFinite]
  have dEq : ready'.memaddrs = ready.memaddrs := by simp [ready', setVarHOLFinite]
  have cEq : ready'.code = ready.code := by simp [ready', setVarHOLFinite]
  have lEq : ready'.locals.lookup (ofString "i") =
      some (ValueHOL.val (HolWordLab.word 0#64)) := by
    simpa [ready'] using wd_loop_counter_binding ready
  have lOther : ∀ x : MlS, x ≠ ofString "i" →
      ready'.locals.lookup x = ready.locals.lookup x := by
    intro x hx
    have hxi : ¬ (ofString "i" = x) := fun h => hx h.symm
    simp [ready', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hxi]
  have main := wdSliceLoop_count_entry DF ready' nwd pl heapBase (allocationEnd heapBase size)
    read X readEq endAligned fit limit smallNwd
    (by rw [endToNat]; omega) readBelow noWrapCells (by rw [dEq, domain]; exact fence) smallDF bigDF lEq
    (by rw [lOther _ (by decide), locals]; exact atNwd)
    (by rw [lOther _ (by decide), locals]; exact atPl)
    (by rw [lOther _ (by decide), locals]; exact freshE)
    (by rw [gEq]; exact wdSlices) (by rw [gEq]; exact heapPtr) (by rw [cEq, postCode]; exact code)
    (by rw [dEq, domain]; exact addrRead) (by rw [mEq, memory]; exact memRead)
    (by rw [clockEq, readyClock]; omega)
  have stateClock : state.clock = ready'.clock + 1 := by
    have := Nat.pos_of_ne_zero clock
    rw [clockEq, readyClock]
    omega
  obtain ⟨mainClock, mainLe, mainNoTO⟩ := main
  have key : ∀ prog : ProgHOL 64,
      evaluateHOLFiniteState
          (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready) prog =
        evaluateHOLFiniteState ready' prog := fun prog => rfl
  refine ⟨ready, run, ?_, ?_, ?_⟩
  · rw [key]
    omega
  · rw [key]
    omega
  · rw [key]
    exact mainNoTO

#print axioms wdSliceLoop_count_alloc
#print axioms wdHeapWord_frontier
#print axioms wdSliceLoop_count_entry

/-- The statement-43 initializer `load [pl + 56]` evaluates to the decoded withdrawal count. -/
theorem wd_count_load_eval {F : Type} (s : PanSemStateFiniteExact 64 F) (pl count : BitVec 64)
    (atPl : s.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (addr : s.memaddrs (pl + 56#64))
    (mem : s.memory (pl + 56#64) = HolWordLab.word count) :
    @evalHOLExact 64 F _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address))
      (.load .one (.op .add [.var .local (ofString "pl"), .const (56#64)])) =
      some (ValueHOL.val (HolWordLab.word count)) := by
  simp [evalHOLExact, evalListHOLExact, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
    memLoadHOLExact, atPl, addr, mem]

end InitECandidate.Runtime
