import InitECandidate.Runtime.HeaderWithdrawalLoopEntry
import InitECandidate.Runtime.HandlerFreeDiscardReaches
import InitECandidate.Runtime.PanWhileNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

/-- A result that only completes or fails is never a return of any value. -/
theorem not_returned_of_control (result : Option (PanSemResultExact 64))
    (h : result = none ∨ result = some .error) :
    ∀ value : ValueHOL 64, result ≠ some (.returned value) := by
  rcases h with h | h <;> rw [h] <;> intro value <;> simp

/-- A `decCall` whose continuation only completes or fails never returns a value out of its
enclosing loop. -/
theorem decCall_noReturn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (resultName : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64)
    (contControl : ∀ (s' : PanSemStateFiniteExact 64 F),
      (evaluateHOLFiniteState s' continuation).1 = none ∨
      (evaluateHOLFiniteState s' continuation).1 = some .error) :
    ∀ value : ValueHOL 64,
      (evaluateHOLFiniteState s
        (.decCall resultName shape function arguments continuation)).1 ≠ some (.returned value) := by
  intro value
  rw [evaluateHOLFiniteState_decCall_total]
  dsimp only
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · simp
        · simp
        · simp
        · split
          · first
            | exact not_returned_of_control _ (Or.inr rfl) value
            | exact not_returned_of_control _ (contControl _) value
          · first
            | exact not_returned_of_control _ (Or.inr rfl) value
            | exact not_returned_of_control _ (contControl _) value
        · simp_all

/-- One withdrawal slice iteration never returns a value out of the loop. -/
theorem wdSliceLoopBody_noReturn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) :
    (evaluateHOLFiniteState s wdSliceLoopBody).1 ≠ some (.returned value) := by
  rw [wdSliceLoopBody]
  exact decCall_noReturn s (ofString "e") (.comb [.one,.one]) (ofString "encode_withdrawal_rlp")
    [.op .add [.load .one (.op .add [.var .local (ofString "pl"), .const (48#64)]),
      .panop .mul [.var .local (ofString "i"), .const (44#64)]]] wdSliceLoopStores
    (fun s' => wdSliceLoopStores_control s') value

/-- The withdrawal slice loop never returns a value out of its enclosing function. -/
theorem wdSliceLoop_noReturn {F : Type} (s : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) :
    (evaluateHOLFiniteState s wdSliceLoop).1 ≠ some (.returned value) := by
  rw [wdSliceLoop]
  exact evaluate_while_no_return wdSliceLoopCondition wdSliceLoopBody
    (fun st v => wdSliceLoopBody_noReturn st v) s value

#print axioms not_returned_of_control
#print axioms decCall_noReturn
#print axioms wdSliceLoopBody_noReturn
#print axioms wdSliceLoop_noReturn

/-- **The statement-46 `Reaches` seam.** From the loop entry state, statement 46 costs at most
`nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)` ticks and reaches the continuation
`actualPayloadHeaderAt 47`; every non-returning terminal outcome of the loop is routed to `StAbort` by
`reaches_seq_of_runBounded`, so no encoder-success premise is needed and only *normal* exit states have
to satisfy `Q`. -/
theorem wdSliceLoop_reaches (DF : Nat) {F : Type} (t : PanSemStateFiniteExact 64 F)
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
    (budget : nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1) ≤ t.clock)
    (Q : PanSemStateFiniteExact 64 F → Prop)
    (normalInv : ∀ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState t wdSliceLoop = (none, post) → Q post) :
    Reaches t (.seq wdSliceLoop (actualPayloadHeaderAt 47)) Q
      (nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) (actualPayloadHeaderAt 47) := by
  have bound : RunBounded t wdSliceLoop (nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) :=
    wdSliceLoop_count_entry DF t nwd pl slices loopHeap read X readEq al fit limit smallNwd
      slicesBelow readBelow noWrapCells fence smallDF bigDF atCounter atNwd atPl freshE atSlices
      atHeap code addrRead memRead budget
  exact reaches_seq_of_runBounded t wdSliceLoop (actualPayloadHeaderAt 47) _ Q bound
    (fun value => wdSliceLoop_noReturn t value) normalInv

/-- The same seam stated on the actual statement-46 program
(`actualPayloadHeaderAt 46 = .seq wdSliceLoop (actualPayloadHeaderAt 47)`). -/
theorem payloadHeader46_reaches (DF : Nat) {F : Type} (t : PanSemStateFiniteExact 64 F)
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
    (budget : nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1) ≤ t.clock)
    (Q : PanSemStateFiniteExact 64 F → Prop)
    (normalInv : ∀ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState t wdSliceLoop = (none, post) → Q post) :
    Reaches t (actualPayloadHeaderAt 46) Q
      (nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) (actualPayloadHeaderAt 47) := by
  rw [source_wd_slice_loop]
  exact wdSliceLoop_reaches DF t nwd pl slices loopHeap read X readEq al fit limit smallNwd
    slicesBelow readBelow noWrapCells fence smallDF bigDF atCounter atNwd atPl freshE atSlices atHeap
    code addrRead memRead budget Q normalInv

#print axioms wdSliceLoop_reaches
#print axioms payloadHeader46_reaches
end InitECandidate.Runtime
