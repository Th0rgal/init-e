import InitECandidate.Runtime.GuestCostCallRule
import InitECandidate.Runtime.ChargeGas
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime.FineCost
open InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact costed events of one expression from its evaluator equation. -/
theorem costedExpression_events {F : Type} (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64)
    (value : Option (ValueHOL 64)) (h : expressionValue s e = value) :
    CostedExpressionRun s e value (expressionEvents s e) := h ▸ costedExpressionRun_total s e

/-- The memory map after writing one word, the exact post-memory of a
`StatementRun.storeValue` step. -/
noncomputable def writeWordMemory {F : Type} (s : PanSemStateFiniteExact 64 F)
    (address value : BitVec 64) : RiscV.Word 64 → HolWordLab 64 :=
  fun current => if current = address then .word value else s.memory current

/-- The successful debit store `ev[64] := gl - amount` of the installed helper,
with the exact work its two expressions and the word write record. -/
theorem chargeGas_storeDebit_run (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left amount : BitVec 64)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hLeft : s.locals.lookup (ofString "gl") = some (.val (.word left)))
    (hAmount : s.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (domain : s.memaddrs (frame + 64)) :
    StatementRun s (.store (fundingAddress 64) gasDebitExpression) none
      { s with memory := writeWordMemory s (frame + 64) (left - amount) }
      (.statement :: (expressionEvents s (fundingAddress 64) ++
        expressionEvents s gasDebitExpression ++
        [.memory (flattenHOL (.val (.word (left - amount)))).length])) := by
  classical
  have dst : CostedExpressionRun s (fundingAddress 64) (some (.val (.word (frame + 64))))
      (expressionEvents s (fundingAddress 64)) :=
    costedExpression_events s _ _ (eval_fundingAddress s frame 64 hFrame)
  have src : CostedExpressionRun s gasDebitExpression (some (.val (.word (left - amount))))
      (expressionEvents s gasDebitExpression) :=
    costedExpression_events s _ _ (eval_gasDebitExpression s left amount hLeft hAmount)
  have write : @panMemStoresHOL 64 _ (frame + 64)
      (flattenHOL (.val (.word (left - amount)))) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory =
      some (writeWordMemory s (frame + 64) (left - amount)) := by
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL]
    rw [if_pos domain]
    rfl
  exact StatementRun.storeValue (destination := fundingAddress 64)
    (source := gasDebitExpression) dst src write

/-- The successful spent store `ev[184] := ev[184] + amount`. -/
theorem chargeGas_storeUsed_run (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame used amount : BitVec 64)
    (hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : s.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (domain : s.memaddrs (frame + 184)) (cell : s.memory (frame + 184) = .word used) :
    StatementRun s (.store (fundingAddress 184) chargeGasUsedExpression) none
      { s with memory := writeWordMemory s (frame + 184) (used + amount) }
      (.statement :: (expressionEvents s (fundingAddress 184) ++
        expressionEvents s chargeGasUsedExpression ++
        [.memory (flattenHOL (.val (.word (used + amount)))).length])) := by
  classical
  have dst : CostedExpressionRun s (fundingAddress 184) (some (.val (.word (frame + 184))))
      (expressionEvents s (fundingAddress 184)) :=
    costedExpression_events s _ _ (eval_fundingAddress s frame 184 hFrame)
  have src : CostedExpressionRun s chargeGasUsedExpression (some (.val (.word (used + amount))))
      (expressionEvents s chargeGasUsedExpression) :=
    costedExpression_events s _ _
      (eval_chargeGasUsedExpression s frame used amount hFrame hAmount domain cell)
  have write : @panMemStoresHOL 64 _ (frame + 184)
      (flattenHOL (.val (.word (used + amount)))) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory =
      some (writeWordMemory s (frame + 184) (used + amount)) := by
    simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL]
    rw [if_pos domain]
    rfl
  exact StatementRun.storeValue (destination := fundingAddress 184)
    (source := chargeGasUsedExpression) dst src write

/-- The helper's final `return 0`. -/
theorem chargeGas_return_run (s : PanSemStateFiniteExact 64 Guest.HostMemory) :
    StatementRun s (.return (.const 0)) (some (.returned (.val (.word 0))))
      (emptyLocalsHOLFinite s)
      (.statement :: (expressionEvents s (.const 0) ++
        [.copy (flattenHOL (.val (.word (0 : BitVec 64)))).length])) := by
  classical
  have expr : CostedExpressionRun s (.const 0) (some (.val (.word 0)))
      (expressionEvents s (.const 0)) :=
    costedExpression_events (F := Guest.HostMemory) s (.const 0) _
      (by simp [expressionValue, evalHOLExact])
  exact StatementRun.returnValue (expression := .const 0) expr
    (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])


/-- The installed helper tail, in the shape the statement traces consume. -/
theorem chargeGasTail_shape : chargeGasTail =
    .seq (.ite chargeGasCheck (.raise (ofString "EvmErr") (.const 4)) .skip)
      (.seq (.store (fundingAddress 64) gasDebitExpression)
        (.seq (.store (fundingAddress 184) chargeGasUsedExpression) (.return (.const 0)))) := by
  cbv

/-- A different frame cell: the two funding offsets never coincide. -/
theorem frameCell_distinct (frame : BitVec 64) : (frame + 64 : BitVec 64) ≠ frame + 184 := by
  intro h
  have h2 : (frame.toNat + 64) % 2 ^ 64 = (frame.toNat + 184) % 2 ^ 64 := by
    simpa [BitVec.toNat_add] using congrArg BitVec.toNat h
  omega

/-- The actual successful execution trace of the installed `charge_gas` helper:
its `dec gl`, its real out-of-gas guard evaluated on the non-throwing branch, the
real debit store, the real spent store, and the real `return 0`. -/
theorem chargeGas_body_run (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left used amount : BitVec 64)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (leftCell : state.memory (frame + 64) = .word left)
    (usedCell : state.memory (frame + 184) = .word used)
    (enough : amount ≤ left) :
    ∃ events, StatementRun state (sourceFunctionBody Guest.guestFn_charge_gas)
      (some (.returned (.val (.word 0))))
      (chargeGasPost state frame left used amount) events := by
  classical
  let entry := setVarHOLFinite (ofString "gl") (.val (.word left)) state
  let s1 := { entry with memory := writeWordMemory entry (frame + 64) (left - amount) }
  let s2 := { s1 with memory := writeWordMemory s1 (frame + 184) (used + amount) }
  have names : ofString "amount" ≠ ofString "gl" := by decide_cbv
  have entryLeft : entry.locals.lookup (ofString "gl") = some (.val (.word left)) := by
    simp [entry, setVarHOLFinite, FUPDATE]
  have entryAmount : entry.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simpa [entry, setVarHOLFinite, FUPDATE, names, Ne.symm names] using hAmount
  have entryUsed : entry.memory (frame + 184) = .word used := by
    simpa [entry, setVarHOLFinite] using usedCell
  have distinct := frameCell_distinct frame
  have s1Amount : s1.locals.lookup (ofString "amount") = some (.val (.word amount)) := by
    simpa [s1] using entryAmount
  have s1Used : s1.memory (frame + 184) = .word used := by
    have other : (frame + 184 : BitVec 64) ≠ frame + 64 := Ne.symm distinct
    simp only [s1, writeWordMemory, if_neg other]
    exact entryUsed
  have init : CostedExpressionRun state (fundingLoad 64) (some (.val (.word left)))
      (expressionEvents state (fundingLoad 64)) :=
    costedExpression_events state _ _ (eval_fundingLoad state frame 64 left hFrame leftDomain leftCell)
  have shapeMatch : shapeEqHOL .one (shapeOfHOLExact (.val (.word left))) = true := by
    simp [shapeOfHOLExact, shapeEqHOL]
  have notLower : ¬ left.toNat < amount.toNat := by
    have h := BitVec.le_def.mp enough
    omega
  have guardValue : expressionValue entry chargeGasCheck = some (.val (.word 0)) := by
    unfold expressionValue
    rw [eval_chargeGasCheck entry left amount entryLeft entryAmount]
    simp [notLower]
  have guard : CostedExpressionRun entry chargeGasCheck (some (.val (.word 0)))
      (expressionEvents entry chargeGasCheck) :=
    costedExpression_events entry chargeGasCheck _ guardValue
  have iteRun : StatementRun entry
      (.ite chargeGasCheck (.raise (ofString "EvmErr") (.const 4)) .skip) none entry
      (.statement :: (expressionEvents entry chargeGasCheck ++ [.statement])) :=
    StatementRun.iteNo (r := none) (post := entry) (bodyEvents := [.statement])
      (yes := .raise (ofString "EvmErr") (.const 4)) (no := .skip)
      guard (StatementRun.skip entry)
  have storeA := chargeGas_storeDebit_run entry frame left amount hFrame entryLeft entryAmount
    (by simpa [entry, setVarHOLFinite] using leftDomain)
  have storeB := chargeGas_storeUsed_run s1 frame used amount
    (by simpa [s1, entry, setVarHOLFinite] using hFrame) s1Amount
    (by simpa [s1, entry, setVarHOLFinite] using usedDomain) s1Used
  have ret := chargeGas_return_run s2
  have tailRun := StatementRun.seqNext storeA (StatementRun.seqNext storeB ret)
  have bodyRun := chargeGasTail_shape.symm ▸ StatementRun.seqNext iteRun tailRun
  rw [source_chargeGas_body]
  exact ⟨_, StatementRun.declareValue (name := ofString "gl") (shape := .one)
    (initializer := fundingLoad 64) (body := chargeGasTail) init shapeMatch bodyRun⟩



/-- Funding form of the helper-body trace: the caller supplies only the funding
relation and the enough-gas fact. -/
theorem chargeGas_body_run_funding (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame amount : BitVec 64) (funding : GasFunding)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding) (enough : amount ≤ funding.left) :
    ∃ events, StatementRun state (sourceFunctionBody Guest.guestFn_charge_gas)
      (some (.returned (.val (.word 0))))
      (chargeGasPost state frame funding.left funding.used amount) events :=
  chargeGas_body_run state frame funding.left funding.used amount hFrame hAmount leftDomain
    usedDomain memory.1 memory.2.1 enough

/-- The actual installed `.call charge_gas [argument]` statement: the callee
entry state, the helper's own traced body, the pure call-exit plan, and the
composed executed work. The reported cost is exactly the local call cost from
`GuestCostCallRule`: statement entry, the evaluated argument, the actual
argument words and frame slot, the traced helper body, and the returned word. -/
theorem chargeGas_call_run (coeff : Work) (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : BitVec 64) (argument : ExpHOL 64) (amount : BitVec 64) (funding : GasFunding)
    (info : Option (Option (VarKind × MlStringHOL) ×
      Option (MlStringHOL × MlStringHOL × ProgHOL 64)))
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word amount)])
    (installed : state.code.lookup (ofString "charge_gas") =
      some ([(ofString "amount", .one)], sourceFunctionBody Guest.guestFn_charge_gas, .one))
    (clock : state.clock ≠ 0)
    (hFrame : state.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (leftDomain : state.memaddrs (frame + 64)) (usedDomain : state.memaddrs (frame + 184))
    (memory : HasGasFunding state frame funding)
    (enough : amount ≤ funding.left) :
    ∃ (bodyEvents : List WorkEvent) (result : Option (PanSemResultExact 64))
      (post : PanSemStateFiniteExact 64 Guest.HostMemory),
      StatementRun (callEntryStateHOLFinite state
        (HolFiniteMapExact.empty.update (ofString "amount", .val (.word amount))))
        (sourceFunctionBody Guest.guestFn_charge_gas) (some (.returned (.val (.word 0))))
        (chargeGasPost (callEntryStateHOLFinite state
          (HolFiniteMapExact.empty.update (ofString "amount", .val (.word amount))))
          frame funding.left funding.used amount) bodyEvents ∧
      callCostPlan state info .one (some (.returned (.val (.word 0))))
        (chargeGasPost (callEntryStateHOLFinite state
          (HolFiniteMapExact.empty.update (ofString "amount", .val (.word amount))))
          frame funding.left funding.used amount) = .done result post ∧
      StatementRun state (.call info (ofString "charge_gas") [argument]) result post
        (callEvents state [argument] [.val (.word amount)] (some (.returned (.val (.word 0))))
          bodyEvents) ∧
      coeff.score (executionWork
        (callEvents state [argument] [.val (.word amount)] (some (.returned (.val (.word 0))))
          bodyEvents)) =
        callLocalCost coeff state [argument] [.val (.word amount)] (some (.returned (.val (.word 0))))
          bodyEvents := by
  classical
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "amount", .val (.word amount))
  obtain ⟨bodyEvents, bodyRun⟩ := chargeGas_body_run_funding
    (state := callEntryStateHOLFinite state callee) (frame := frame) (amount := amount)
    (funding := funding) hFrame
    (by simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE])
    leftDomain usedDomain memory enough
  let bodyPost := chargeGasPost (callEntryStateHOLFinite state callee) frame funding.left
    funding.used amount
  let value : ValueHOL 64 := .val (.word 0)
  have shape : shapeEqHOL (shapeOfHOLExact value) .one = true := by
    simp [value, shapeOfHOLExact, shapeEqHOL]
  have plan : ∃ result post, callCostPlan state info .one (some (.returned value)) bodyPost =
      .done result post := by
    cases info with
    | none =>
        exact ⟨some (.returned value), emptyLocalsHOLFinite bodyPost, by simp [callCostPlan, shape]⟩
    | some packed =>
        obtain ⟨assignment, handler⟩ := packed
        cases assignment with
        | none =>
            exact ⟨none, { bodyPost with locals := state.locals }, by simp [callCostPlan, shape]⟩
        | some binding =>
            obtain ⟨kind, name⟩ := binding
            cases valid : isValidValueHOLExact state.toExact kind name value with
            | true =>
                exact ⟨none, setKvarHOLFinite kind name value { bodyPost with locals := state.locals },
                  by simp [callCostPlan, shape, valid]⟩
            | false =>
                exact ⟨some .error, bodyPost, by simp [callCostPlan, shape, valid]⟩
  obtain ⟨result, post, planEq⟩ := plan
  have lookup := pan_single_word_lookup state.code.lookup (ofString "charge_gas")
    (ofString "amount") (sourceFunctionBody Guest.guestFn_charge_gas) amount installed
  have call := call_statement_work (callee := callee) (info := info) (returnShape := .one)
    (function := ofString "charge_gas") (body := sourceFunctionBody Guest.guestFn_charge_gas)
    (bodyResult := some (.returned value)) (bodyPost := bodyPost)
    coeff arguments lookup clock bodyRun planEq
  exact ⟨bodyEvents, result, post, bodyRun, planEq, call.1, call.2⟩



/-- An empty event list records no work. -/
theorem executionWork_nil_score (coeff : Work) :
    coeff.score (executionWork ([] : List WorkEvent)) = 0 := by
  simp [executionWork, Work.score]

/-- The exact recorded work of one successful `charge_gas` helper execution, in
source order: the `dec gl` initialiser and its frame slot, the real out-of-gas
guard, the debit store, the spent store, the final `return 0`, and the restored
previous `gl` value. -/
noncomputable def chargeGasBodyEvents (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left used amount : BitVec 64) : List WorkEvent :=
  let entry := setVarHOLFinite (ofString "gl") (.val (.word left)) s
  let s1 := { entry with memory := writeWordMemory entry (frame + 64) (left - amount) }
  let s2 := { s1 with memory := writeWordMemory s1 (frame + 184) (used + amount) }
  let iteEvents := .statement :: (expressionEvents entry chargeGasCheck ++ [.statement])
  let storeA := .statement :: (expressionEvents entry (fundingAddress 64) ++
    expressionEvents entry gasDebitExpression ++
    [.memory (flattenHOL (.val (.word (left - amount)))).length])
  let storeB := .statement :: (expressionEvents s1 (fundingAddress 184) ++
    expressionEvents s1 chargeGasUsedExpression ++
    [.memory (flattenHOL (.val (.word (used + amount)))).length])
  let ret := .statement :: (expressionEvents s2 (.const 0) ++
    [.copy (flattenHOL (.val (.word (0 : BitVec 64)))).length])
  let tailEvents := .statement :: (storeA ++ (.statement :: (storeB ++ ret)))
  let bodyEvents := .statement :: (iteEvents ++ tailEvents)
  .statement ::
    (((expressionEvents s (fundingLoad 64) ++
        [.copy (flattenHOL (.val (.word left))).length, .frame 1]) ++ bodyEvents) ++
      [.copy (((s.locals.lookup (ofString "gl")).map
        (fun previous => (flattenHOL previous).length)).getD 0)])

/-- Explicit coefficient price of one successful `charge_gas` helper execution.
Sixteen statement entries cover the helper's own three statements together with
the `seq`/`ite` structure the compiler emits around them, so the coefficient
multiplying `statements` is an over-count rather than a sharp count; every other
term is the exact recorded size of the real work: each compiled expression's own
cost, the copied `gl` word, the frame slot, the two word writes, the returned
word, and the restored previous `gl` value. -/
theorem chargeGasBodyEvents_score (coeff : Work)
    (s : PanSemStateFiniteExact 64 Guest.HostMemory) (frame left used amount : BitVec 64) :
    coeff.score (executionWork (chargeGasBodyEvents s frame left used amount)) ≤
      let entry := setVarHOLFinite (ofString "gl") (.val (.word left)) s
      let s1 := { entry with memory := writeWordMemory entry (frame + 64) (left - amount) }
      let s2 := { s1 with memory := writeWordMemory s1 (frame + 184) (used + amount) }
      16 * coeff.statements +
        expressionCost coeff s (fundingLoad 64) +
        coeff.movedWords * (flattenHOL (.val (.word left))).length + coeff.frameSlots +
        expressionCost coeff entry chargeGasCheck +
        expressionCost coeff entry (fundingAddress 64) +
        expressionCost coeff entry gasDebitExpression +
        coeff.memoryAccesses * (flattenHOL (.val (.word (left - amount)))).length +
        expressionCost coeff s1 (fundingAddress 184) +
        expressionCost coeff s1 chargeGasUsedExpression +
        coeff.memoryAccesses * (flattenHOL (.val (.word (used + amount)))).length +
        expressionCost coeff s2 (.const 0) +
        coeff.movedWords * (flattenHOL (.val (.word (0 : BitVec 64)))).length +
        coeff.movedWords * (((s.locals.lookup (ofString "gl")).map
          (fun previous => (flattenHOL previous).length)).getD 0) := by
  unfold chargeGasBodyEvents expressionCost
  simp only [executionWork_score_cons, executionWork_score_append, score_statement,
    score_copy, score_frame, score_memory, score_singleton, score_expression,
    executionWork_nil_score, List.append_nil]
  omega

#print axioms chargeGasBodyEvents_score
#print axioms chargeGas_call_run
#print axioms chargeGas_body_run


#print axioms chargeGas_storeDebit_run
#print axioms chargeGas_storeUsed_run
#print axioms chargeGas_return_run
end InitECandidate.Runtime.FineCost
