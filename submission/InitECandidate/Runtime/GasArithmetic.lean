import InitECandidate.Runtime.SourceClock

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact subtraction expression in `Guest.guestFn_charge_gas`. -/
def gasDebitExpression : ExpHOL 64 :=
  .op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")]

/-- Extract the first store's value from the authoritative helper AST. -/
def chargeGasStoredDebit : ExpHOL 64 :=
  match sourceFunctionBody Guest.guestFn_charge_gas with
  | .dec _ _ _ (.seq _ (.seq (.store _ debit) _)) => debit
  | _ => .const 0

theorem chargeGasStoredDebit_eq : chargeGasStoredDebit = gasDebitExpression := by cbv

theorem eval_gasDebitExpression (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (available amount : BitVec 64)
    (hAvailable : state.locals.lookup (ofString "gl") = some (.val (.word available)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount))) :
    @evalHOLExact 64 Guest.HostMemory _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) gasDebitExpression =
      some (.val (.word (available - amount))) := by
  classical
  simp [gasDebitExpression, evalHOLExact, evalListHOLExact, toExact,
    hAvailable, hAmount, wordOpHOL, wordOp, valueIsWord, valueWord]

theorem eval_chargeGasStoredDebit (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (available amount : BitVec 64)
    (hAvailable : state.locals.lookup (ofString "gl") = some (.val (.word available)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount))) :
    @evalHOLExact 64 Guest.HostMemory _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) chargeGasStoredDebit =
      some (.val (.word (available - amount))) := by
  rw [chargeGasStoredDebit_eq]
  exact eval_gasDebitExpression state available amount hAvailable hAmount

/-- The unsigned out-of-gas guard extracted from the same authoritative AST. -/
def chargeGasCheck : ExpHOL 64 :=
  match sourceFunctionBody Guest.guestFn_charge_gas with
  | .dec _ _ _ (.seq (.ite condition _ _) _) => condition
  | _ => .const 1

theorem chargeGasCheck_eq : chargeGasCheck =
    .cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount")) := by cbv

theorem eval_chargeGasCheck (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (available amount : BitVec 64)
    (hAvailable : state.locals.lookup (ofString "gl") = some (.val (.word available)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount))) :
    @evalHOLExact 64 Guest.HostMemory _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) chargeGasCheck =
      some (.val (.word (if available.toNat < amount.toNat then 1 else 0))) := by
  classical
  rw [chargeGasCheck_eq]
  simp [evalHOLExact, toExact, hAvailable, hAmount,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def]

/-- Taking the helper's non-throwing branch proves the unsigned debit bound. -/
theorem chargeGas_guard_implies_enough (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (available amount : BitVec 64)
    (hAvailable : state.locals.lookup (ofString "gl") = some (.val (.word available)))
    (hAmount : state.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (guard : @evalHOLExact 64 Guest.HostMemory _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) chargeGasCheck =
        some (.val (.word 0))) : amount ≤ available := by
  rw [eval_chargeGasCheck state available amount hAvailable hAmount] at guard
  by_cases enough : amount ≤ available
  · exact enough
  · have notEnough : ¬ amount.toNat ≤ available.toNat := by
      simpa only [BitVec.le_def] using enough
    have lower : available.toNat < amount.toNat := by omega
    simp [lower] at guard

/-- The actual unsigned guard excludes subtraction wraparound. -/
theorem gasDebit_toNat (available amount : BitVec 64) (enough : amount ≤ available) :
    (available - amount).toNat = available.toNat - amount.toNat := by
  exact BitVec.toNat_sub_of_le enough

theorem gasDebit_strict (available amount : BitVec 64)
    (enough : amount ≤ available) (positive : 0 < amount.toNat) :
    (available - amount).toNat < available.toNat := by
  rw [gasDebit_toNat available amount enough]
  have h := BitVec.le_def.mp enough
  omega

/-- Cumulative gas spent is conserved by successful charging. A separate
invariant must establish this no-wrap premise at every frame transition. -/
theorem gasDebit_conservation (available spent amount : BitVec 64)
    (enough : amount ≤ available)
    (noWrap : spent.toNat + amount.toNat < 2 ^ 64) :
    (available - amount).toNat + (spent + amount).toNat =
      available.toNat + spent.toNat := by
  rw [gasDebit_toNat available amount enough, BitVec.toNat_add,
    Nat.mod_eq_of_lt noWrap]
  have h := BitVec.le_def.mp enough
  omega

/-- Under the regular-gas potential invariant, charging cannot wrap the spent
counter. This discharges the arithmetic side condition rather than assuming it. -/
theorem charge_noWrap (available spent amount : BitVec 64)
    (enough : amount ≤ available)
    (potential : available.toNat + spent.toNat ≤ 200000000) :
    spent.toNat + amount.toNat < 2 ^ 64 := by
  have bound := BitVec.le_def.mp enough
  omega

theorem charge_preserves_potential (available spent amount : BitVec 64)
    (enough : amount ≤ available)
    (potential : available.toNat + spent.toNat ≤ 200000000) :
    (available - amount).toNat + (spent + amount).toNat ≤ 200000000 := by
  rw [gasDebit_conservation available spent amount enough
    (charge_noWrap available spent amount enough potential)]
  exact potential

/-- A trace of successful *positive* debits with no interspersed credit.
Credits and frame changes are deliberately excluded here: the global runtime
proof must account for them with a larger potential, not assume them away. -/
inductive PositiveDebitTrace : BitVec 64 → BitVec 64 → Nat → Prop
  | done (available : BitVec 64) : PositiveDebitTrace available available 0
  | debit (available amount final : BitVec 64) (count : Nat)
      (enough : amount ≤ available) (positive : 0 < amount.toNat)
      (rest : PositiveDebitTrace (available - amount) final count) :
      PositiveDebitTrace available final (count + 1)

theorem positiveDebitTrace_bound {initial final : BitVec 64} {count : Nat}
    (trace : PositiveDebitTrace initial final count) :
    count + final.toNat ≤ initial.toNat := by
  induction trace with
  | done available => simp
  | debit available amount final count enough positive rest ih =>
    rw [gasDebit_toNat available amount enough] at ih
    have amountBound := BitVec.le_def.mp enough
    omega

theorem positiveDebitTrace_200M {initial final : BitVec 64} {count : Nat}
    (trace : PositiveDebitTrace initial final count)
    (gas : initial.toNat ≤ 200000000) : count ≤ 200000000 := by
  have bound := positiveDebitTrace_bound trace
  omega

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.eval_gasDebitExpression
#print axioms InitECandidate.Runtime.gasDebit_conservation

#print axioms InitECandidate.Runtime.positiveDebitTrace_200M
#print axioms InitECandidate.Runtime.chargeGas_guard_implies_enough
