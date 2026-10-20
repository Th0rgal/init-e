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

/-- The statement-44 allocator argument `nwd * 16 + 16` evaluates to the slice-array size. -/
theorem wd_slice_size_args {F : Type} (s : PanSemStateFiniteExact 64 F) (nwd size : BitVec 64)
    (atNwd : s.locals.lookup (ofString "nwd") = some (ValueHOL.val (HolWordLab.word nwd)))
    (sizeVal : size = nwd * 16#64 + 16#64)
    (fitSize : nwd.toNat * 16 + 16 < 2 ^ 64) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.op .add [(.panop .mul [.var .local (ofString "nwd"), .const (16#64)]),
        .const (16#64)]] = some [ValueHOL.val (HolWordLab.word size)] := by
  subst sizeVal
  rw [evalListHOLFinite_eq_toExact]
  simp [evalListHOLExact, evalHOLExact, panOpHOL, wordOpHOL, wordOp, valueIsWord, valueWord, atNwd,
    BitVec.toNat_mul, BitVec.toNat_add]

#print axioms wd_slice_size_args

/-- **Statements 43 → 46 as one `Reaches`, ending at the actual statement-47 continuation.** Starting
from the statement-43 entry state, the count declaration costs nothing, the statement-44 allocator call
costs one tick, the statement-45 counter declaration costs nothing, and statement 46's loop costs
`nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)`; the whole prefix therefore reaches
`actualPayloadHeaderAt 47` within `1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)` ticks.
Non-returning outcomes (including an encoder error inside the loop) are routed to `StAbort` by
`reaches_seq_of_runBounded`, so there is no encoder-success premise. The builder callee after statement
47 is not touched. -/
theorem payloadHeader43_reaches (DF : Nat) {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nwd size loopHeap pl read X : BitVec 64)
    (readEq : read = pl + 48#64)
    (atPl : s.locals.lookup (ofString "pl") = some (ValueHOL.val (HolWordLab.word pl)))
    (freshE : s.locals.lookup (ofString "e") = none)
    (atSlices : s.globals.lookup (ofString "wd_rlp_slices") =
      some (ValueHOL.val (HolWordLab.word loopHeap)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") =
      some (ValueHOL.val (HolWordLab.word loopHeap)))
    (code : s.code = originalRuntimeCode) (clock : s.clock ≠ 0)
    (countAddr : s.memaddrs (pl + 56#64))
    (countMem : s.memory (pl + 56#64) = HolWordLab.word nwd)
    (sizeVal : size = nwd * 16#64 + 16#64)
    (al : loopHeap.toNat % 8 = 0) (sizeAl : size.toNat % 8 = 0)
    (bounded : loopHeap.toNat + size.toNat ≤ 33806089496)
    (fitSize : nwd.toNat * 16 + 16 < 2 ^ 64)
    (fit : (allocationEnd loopHeap size).toNat + 64 * nwd.toNat + 64 < 2 ^ 64)
    (limit : (allocationEnd loopHeap size).toNat + 64 * nwd.toNat + 64 ≤ 33806089496)
    (smallNwd : nwd.toNat + 1 < 2 ^ 63)
    (readBelow : read.toNat < loopHeap.toNat)
    (noWrapCells : loopHeap.toNat + 16 * nwd.toNat + 8 < 2 ^ 64)
    (fence : Fence s.memaddrs DF) (smallDF : DF + 8 ≤ 2 ^ 62) (bigDF : 33806089496 ≤ DF)
    (addrRead : s.memaddrs read) (memRead : s.memory read = HolWordLab.word X)
    (budget : 1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1) ≤ s.clock) :
    Reaches s (actualPayloadHeaderAt 43) (fun _ => True)
      (1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) (actualPayloadHeaderAt 47) := by
  let declared : PanSemStateFiniteExact 64 F :=
    setVarHOLFinite (ofString "nwd") (ValueHOL.val (HolWordLab.word nwd)) s
  have atNwdDeclared : declared.locals.lookup (ofString "nwd") =
      some (ValueHOL.val (HolWordLab.word nwd)) := by
    simp [declared, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have declVars : declared.globals = s.globals ∧ declared.memory = s.memory ∧
      declared.memaddrs = s.memaddrs ∧ declared.code = s.code ∧ declared.clock = s.clock :=
    ⟨by simp [declared, setVarHOLFinite], by simp [declared, setVarHOLFinite],
      by simp [declared, setVarHOLFinite], by simp [declared, setVarHOLFinite],
      by simp [declared, setVarHOLFinite]⟩
  -- statement 43
  have h43 : Reaches s (actualPayloadHeaderAt 43) (fun t => t = declared) 0
      (actualPayloadHeaderAt 44) := by
    rw [source_actual_payload_header_withdrawal_count]
    refine reaches_dec s (ofString "nwd")
      (.load .one (.op .add [.var .local (ofString "pl"), .const (56#64)]))
      (actualPayloadHeaderAt 44) (fun t => t = declared) ?_
    intro v hv
    rw [wd_count_load_eval s pl nwd atPl countAddr countMem] at hv
    injection hv with hval
    exact ⟨nwd, hval.symm, rfl⟩
  -- statements 44..46 from the declaration state
  have h44 : ∀ E : PanSemStateFiniteExact 64 F, E = declared →
      Reaches E (actualPayloadHeaderAt 44) (fun _ => True)
        (1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) (actualPayloadHeaderAt 47) := by
    intro E hE
    subst hE
    have args := wd_slice_size_args declared nwd size atNwdDeclared sizeVal fitSize
    obtain ⟨ready, runAlloc, mainClock, mainLe, mainNoTO⟩ :=
      wdSliceLoop_count_alloc DF declared nwd size loopHeap pl read X sizeVal readEq atNwdDeclared
        (by rw [declVars.1]; exact atSlices) (by rw [declVars.1]; exact atHeap)
        (by rw [declVars.2.2.2.1]; exact code) (by rw [declVars.2.2.2.2]; exact clock) args al
        sizeAl bounded fit limit smallNwd readBelow noWrapCells (by rw [declVars.2.2.1]; exact fence)
        smallDF bigDF (by simp [declared, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show (ofString "nwd") ≠ ofString "pl" by decide]; exact atPl)
        (by simp [declared, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show (ofString "nwd") ≠ ofString "e" by decide]; exact freshE)
        (by rw [declVars.2.2.1]; exact addrRead) (by rw [declVars.2.1]; exact memRead)
        (by rw [declVars.2.2.2.2]; omega)
    obtain ⟨ready2, run2, clocks0, memory0, locals0, postCode0, domain0, _, slicesLookup, heapLookup, _⟩ :=
      evaluate_alloc_global_call declared _ loopHeap size loopHeap (ofString "wd_rlp_slices") args
        (by rw [declVars.2.2.2.1]; exact code) (by rw [declVars.2.2.2.2]; exact clock)
        (by rw [declVars.1]; exact atHeap) (by rw [declVars.1]; exact atSlices) (by decide)
        (allocationGuard_of_sum_bound loopHeap size bounded)
        (by rw [allocationEnd_aligned_toNat loopHeap size bounded al sizeAl]; omega)
    have readyEq : ready = ready2 := by
      have h : (none, ready) = (none, ready2) := runAlloc.symm.trans run2
      exact congrArg Prod.snd h
    have readyClock : ready.clock = declared.clock - 1 := by
      simpa [readyEq] using clocks0
    have readyLocals : ready.locals = declared.locals := by
      simpa [readyEq] using locals0
    have readySlices : ready.globals.lookup (ofString "wd_rlp_slices") =
        some (ValueHOL.val (HolWordLab.word loopHeap)) := by
      simpa [readyEq] using slicesLookup
    have readyHeap : ready.globals.lookup (ofString "heap_ptr") =
        some (ValueHOL.val (HolWordLab.word (allocationEnd loopHeap size))) := by
      simpa [readyEq] using heapLookup
    have readyMemaddrs : ready.memaddrs = declared.memaddrs := by
      simpa [readyEq] using domain0
    have readyMemory : ready.memory = declared.memory := by
      simpa [readyEq] using memory0
    -- statement 44: the allocator call, one tick
    have h44a : Reaches declared (actualPayloadHeaderAt 44) (fun t => t = ready) 1
        (actualPayloadHeaderAt 45) := by
      rw [source_actual_payload_header_withdrawal_slices]
      refine reaches_seq declared _ _ 1 (fun t => t = ready) ?_
      exact Or.inl ⟨ready, rfl, by omega, by omega, runAlloc⟩
    -- statement 45: the counter declaration, free
    let ready' : PanSemStateFiniteExact 64 F :=
      setVarHOLFinite (ofString "i") (ValueHOL.val (HolWordLab.word 0#64)) ready
    have h45 : Reaches ready (actualPayloadHeaderAt 45) (fun t => t = ready') 0
        (actualPayloadHeaderAt 46) := by
      rw [source_actual_payload_header_loop_counter]
      refine reaches_dec ready (ofString "i") (.const (0#64)) (actualPayloadHeaderAt 46)
        (fun t => t = ready') ?_
      intro v hv
      obtain rfl : v = ValueHOL.val (HolWordLab.word 0#64) := by
        simpa [evalHOLExact] using hv.symm
      exact ⟨0#64, rfl, rfl⟩
    -- statement 46: the loop
    have readyVars : ready'.globals = ready.globals ∧ ready'.memory = ready.memory ∧
        ready'.memaddrs = ready.memaddrs ∧ ready'.code = ready.code ∧
        ready'.clock = ready.clock :=
      ⟨by simp [ready', setVarHOLFinite], by simp [ready', setVarHOLFinite],
        by simp [ready', setVarHOLFinite], by simp [ready', setVarHOLFinite],
        by simp [ready', setVarHOLFinite]⟩
    have atCounter' : ready'.locals.lookup (ofString "i") =
        some (ValueHOL.val (HolWordLab.word 0#64)) := by
      simp [ready', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have atNwd' : ready'.locals.lookup (ofString "nwd") =
        some (ValueHOL.val (HolWordLab.word nwd)) := by
      rw [show ready'.locals.lookup (ofString "nwd") = ready.locals.lookup (ofString "nwd") from by
        simp [ready', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "nwd" by decide]]
      rw [readyLocals]
      exact atNwdDeclared
    have atPl' : ready'.locals.lookup (ofString "pl") =
        some (ValueHOL.val (HolWordLab.word pl)) := by
      rw [show ready'.locals.lookup (ofString "pl") = ready.locals.lookup (ofString "pl") from by
        simp [ready', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "pl" by decide]]
      rw [readyLocals]
      simpa [declared, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nwd" ≠ ofString "pl" by decide] using atPl
    have freshE' : ready'.locals.lookup (ofString "e") = none := by
      rw [show ready'.locals.lookup (ofString "e") = ready.locals.lookup (ofString "e") from by
        simp [ready', setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "i" ≠ ofString "e" by decide]]
      rw [readyLocals]
      simpa [declared, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        show ofString "nwd" ≠ ofString "e" by decide] using freshE
    have h46 : Reaches ready' (actualPayloadHeaderAt 46) (fun _ => True)
        (nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) (actualPayloadHeaderAt 47) :=
      payloadHeader46_reaches DF ready' nwd pl loopHeap (allocationEnd loopHeap size) read X readEq
        (by rw [allocationEnd_aligned_toNat loopHeap size bounded al sizeAl]; omega) fit limit smallNwd
        (by rw [allocationEnd_aligned_toNat loopHeap size bounded al sizeAl]; omega) readBelow
        noWrapCells (by rw [readyVars.2.2.1]; rw [readyMemaddrs]; exact fence) smallDF bigDF
        atCounter' atNwd' atPl' freshE'
        (by rw [readyVars.1]; exact readySlices)
        (by rw [readyVars.1]; exact readyHeap)
        (by rw [readyVars.2.2.2.1, readyEq, postCode0, declVars.2.2.2.1]; exact code)
        (by rw [readyVars.2.2.1]; rw [readyMemaddrs]; rw [declVars.2.2.1]; exact addrRead)
        (by rw [readyVars.2.1]; rw [readyMemory]; rw [declVars.2.1]; exact memRead)
        (by rw [readyVars.2.2.2.2]; rw [readyClock]; omega)
        (fun _ => True) (fun _ _ => trivial)
    -- 44 → 45 → 46
    have hMid : Reaches declared (actualPayloadHeaderAt 44) (fun _ => True)
        (1 + (0 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)))
        (actualPayloadHeaderAt 47) := by
      refine reaches_trans declared (actualPayloadHeaderAt 44) (actualPayloadHeaderAt 45)
        (actualPayloadHeaderAt 47) (fun t => t = ready) (fun _ => True) 1
        (0 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) h44a ?_
      intro E hE
      rw [hE]
      exact reaches_trans ready (actualPayloadHeaderAt 45) (actualPayloadHeaderAt 46)
        (actualPayloadHeaderAt 47) (fun t => t = ready') (fun _ => True) 0
        (nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) h45
        (fun E' hE' => by rw [hE']; exact h46)
    have := mainClock
    exact reaches_mono declared (actualPayloadHeaderAt 44) (actualPayloadHeaderAt 47)
      (fun _ => True) (fun _ => True)
      (1 + (0 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)))
      (1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) (by omega)
      (fun _ _ => trivial) hMid
  -- 43 → 44..46
  exact reaches_mono s (actualPayloadHeaderAt 43) (actualPayloadHeaderAt 47)
    (fun _ => True) (fun _ => True)
    (0 + (1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)))
    (1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) (by omega) (fun _ _ => trivial)
    (reaches_trans s (actualPayloadHeaderAt 43) (actualPayloadHeaderAt 44) (actualPayloadHeaderAt 47)
      (fun t => t = declared) (fun _ => True) 0
      (1 + nwd.toNat * ((encodeWithdrawalSourceCost DF + 1) + 1)) h43 h44)

#print axioms payloadHeader43_reaches
end InitECandidate.Runtime
