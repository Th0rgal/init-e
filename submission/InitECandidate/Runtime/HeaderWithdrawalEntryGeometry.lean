import InitECandidate.Runtime.HeaderWithdrawalEntryFacts
import InitECandidate.Runtime.AllocationAligned
import InitECandidate.Runtime.AllocationGlobalCall
import InitECandidate.Runtime.AccountOptionalArena
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Statement 44's allocation: the slice array starts at the old heap frontier, and the frontier
moves to the exact, 8-aligned end `slices + size`. -/
theorem wd_slices_alloc_end (slices size : BitVec 64)
    (al : slices.toNat % 8 = 0) (sizeAl : size.toNat % 8 = 0)
    (bounded : slices.toNat + size.toNat ≤ 33806089496) :
    (allocationEnd slices size).toNat = slices.toNat + size.toNat ∧
    (allocationEnd slices size).toNat % 8 = 0 := by
  have exact := allocationEnd_aligned_toNat slices size bounded al sizeAl
  refine ⟨exact, ?_⟩
  rw [exact]
  omega

/-- Words below the slice array never collide with any 16-byte slice cell of the run. -/
theorem wd_slice_cells_below (read slices : BitVec 64) (nwd j : Nat)
    (below : read.toNat < slices.toNat)
    (noWrap : slices.toNat + 16 * nwd + 8 < 2^64)
    (hj : j ≤ nwd) :
    read ≠ slices + (BitVec.ofNat 64 j) * 16#64 ∧
    read ≠ slices + (BitVec.ofNat 64 j) * 16#64 + 8#64 := by
  have jFit : j * 16 < 2^64 := by omega
  have s16 : (16#64 : BitVec 64).toNat = 16 := by decide
  have s8 : (8#64 : BitVec 64).toNat = 8 := by decide
  have cellVal : ((BitVec.ofNat 64 j) * 16#64 : BitVec 64).toNat = j * 16 := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2^64), s16,
      Nat.mod_eq_of_lt jFit]
  have cellNat : (slices + (BitVec.ofNat 64 j) * 16#64).toNat = slices.toNat + j * 16 := by
    rw [BitVec.toNat_add, cellVal, Nat.mod_eq_of_lt (by omega)]
  have cellNat8 : (slices + (BitVec.ofNat 64 j) * 16#64 + 8#64).toNat =
      slices.toNat + j * 16 + 8 := by
    rw [BitVec.toNat_add, cellNat, s8, Nat.mod_eq_of_lt (by omega)]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [cellNat] at this
    omega
  · intro h
    have := congrArg BitVec.toNat h
    rw [cellNat8] at this
    omega

/-- Words below the arena are outside every 64-byte heap word window of the run. -/
theorem wd_heap_window_below (heapBase w : BitVec 64) (nwd : Nat)
    (al : heapBase.toNat % 8 = 0)
    (below : w.toNat < heapBase.toNat)
    (fit : heapBase.toNat + 64 * nwd + 64 < 2^64) :
    ∀ j, j ≤ nwd → ¬ MWin (wdHeapWord heapBase j) 64 w := by
  intro j hj
  have jFit : heapBase.toNat + 64 * j < 2^64 := by omega
  have toNatj : (wdHeapWord heapBase j).toNat = heapBase.toNat + 64 * j :=
    wdHeapWord_toNat heapBase j jFit
  apply mwin_above (D := wdHeapWord heapBase j) (N := 64)
  · rw [toNatj]; omega
  · rw [toNatj]; omega
  · rw [toNatj]; omega

/-- Statement 46 with the withdrawal-loop entry geometry derived from the actual earlier statements:
`i` starts at the declared `0`, the slice array and the loop allocations all sit above the payload
area, so every per-iteration window and every slice cell misses both watched cells. -/
theorem payloadHeader46_window_geometry {F : Type} (t : PanSemStateFiniteExact 64 F)
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
    (fitRange : heapBase.toNat + 64 * nwd.toNat + 128 < 2^64)
    (limit : heapBase.toNat + 64 * nwd.toNat + 64 ≤ 33806089496)
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
  refine payloadHeader46_window_entry t 0#64 nwd pl slices heapBase w read X readEq ?_ atNwd atPl
    freshE atSlices atHeap code aligned (by omega) limit ?_ smallNwd ?_ ?_ addrRead ?_ ?_ memRead tail
  · simpa using atCounter
  · simpa using (show (0#64 : BitVec 64).toNat = 0 from rfl)
  · exact mwin_above (D := heapBase) (N := 64 * nwd.toNat + 64) (by omega) aligned (by omega)
  · exact mwin_above (D := heapBase) (N := 64 * nwd.toNat + 64) (by omega) aligned (by omega)
  · intro j hj
    have cells := wd_slice_cells_below w slices nwd.toNat j (by omega) noWrapCells hj
    simpa [BitVec.zero_add] using cells
  · intro j hj
    have cells := wd_slice_cells_below read slices nwd.toNat j (by omega) noWrapCells hj
    simpa [BitVec.zero_add] using cells

#print axioms payloadHeader46_window_geometry
#print axioms wd_slices_alloc_end
#print axioms wd_slice_cells_below
#print axioms wd_heap_window_below
/-- Statement 44's actual allocator call (into the global `wd_rlp_slices`) supplies the loop's arena
geometry: the slice array starts exactly at the old heap frontier, the frontier advances to the exact
8-aligned end, and the caller's memory, address domain, locals and code are untouched. -/
theorem wd_slices_alloc_entry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (nwd size heapBase : BitVec 64)
    (sizeVal : size = nwd * 16#64 + 16#64)
    (atNwd : state.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)))
    (atGlobal : state.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word heapBase)))
    (atHeap : state.globals.lookup (ofString "heap_ptr") =
      some (ValueHOL.val (HolWordLab.word heapBase)))
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.op .add [(.panop .mul [.var .local (ofString "nwd"), .const (16#64)]),
        .const (16#64)]] = some [.val (.word size)])
    (al : heapBase.toNat % 8 = 0) (sizeAl : size.toNat % 8 = 0)
    (bounded : heapBase.toNat + size.toNat ≤ 33806089496) :
    ∃ ready,
      evaluateHOLFiniteState state (.call (some ((some (.global,ofString "wd_rlp_slices")),none))
        (ofString "alloc") [.op .add [(.panop .mul [.var .local (ofString "nwd"), .const (16#64)]),
          .const (16#64)]]) = (none, ready) ∧
      ready.memory = state.memory ∧ ready.memaddrs = state.memaddrs ∧
      ready.locals = state.locals ∧ ready.code = state.code ∧
      ready.globals.lookup (ofString "wd_rlp_slices") =
        some (ValueHOL.val (HolWordLab.word heapBase)) ∧
      ready.globals.lookup (ofString "heap_ptr") =
        some (ValueHOL.val (HolWordLab.word (allocationEnd heapBase size))) ∧
      (allocationEnd heapBase size).toNat = heapBase.toNat + size.toNat ∧
      (allocationEnd heapBase size).toNat % 8 = 0 := by
  have endExact := wd_slices_alloc_end heapBase size al sizeAl bounded
  have finishBound : (allocationEnd heapBase size).toNat ≤ 33806089496 := by
    rw [endExact.1]; omega
  obtain ⟨ready,run,_,memory,locals,postCode,domain,_,wdSlices,heapPtr,_⟩ :=
    evaluate_alloc_global_call state _ heapBase size heapBase (ofString "wd_rlp_slices") args code clock
      atHeap atGlobal (by decide) (allocationGuard_of_sum_bound heapBase size bounded) finishBound
  exact ⟨ready,run,memory,domain,locals,postCode,wdSlices,heapPtr,endExact.1,endExact.2⟩

/-- Statement 45 binds the loop counter: the state statement 46 starts from has `i` declared `0`. -/
theorem wd_loop_counter_binding {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) state).locals.lookup
        (ofString "i") = some (ValueHOL.val (HolWordLab.word 0#64)) := by
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- Statement 43 binds the decoded withdrawal count for the whole serialization tail. -/
theorem wd_nwd_binding {F : Type} (state : PanSemStateFiniteExact 64 F) (nwd : BitVec 64) :
    (setVarHOLFinite (ofString "nwd") (ValueHOL.val (HolWordLab.word nwd)) state).locals.lookup
        (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)) := by
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- Declaring a local does not move the memory: the watched payload words stay put across
statements 43–45. -/
theorem wd_declaration_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (value : ValueHOL 64) :
    (setVarHOLFinite name value state).memory = state.memory := by
  simp [setVarHOLFinite]

/-- Declaring a local does not change the address domain, so the aligned-cell domain is carried from
the payload header prologue to statement 46 unchanged. -/
theorem wd_declaration_memaddrs {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (value : ValueHOL 64) :
    (setVarHOLFinite name value state).memaddrs = state.memaddrs := by
  simp [setVarHOLFinite]

/-- Declaring a local does not change the code, so the original runtime code survives 43–45. -/
theorem wd_declaration_code {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (value : ValueHOL 64) :
    (setVarHOLFinite name value state).code = state.code := by
  simp [setVarHOLFinite]

end InitECandidate.Runtime
