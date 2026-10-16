import InitECandidate.Runtime.MinCall

namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def wordAddSat (left right : BitVec 64) : BitVec 64 :=
  if (left + right).toNat < left.toNat then 18446744073709551615 else left + right

theorem source_addSat_body : sourceFunctionBody Guest.guestFn_add_sat =
    .dec (ofString "s") .one (.op .add [.var .local (ofString "a"), .var .local (ofString "b")])
      (.seq (.ite (.cmp .lower (.var .local (ofString "s")) (.var .local (ofString "a")))
        (.return (.const 18446744073709551615)) .skip) (.return (.var .local (ofString "s")))) := by cbv

/-- The saturating helper executes without consuming clock. Its local scope
restoration remains explicit for use in arbitrary evaluator states. -/
theorem evaluate_source_addSat {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (left right : BitVec 64)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word left)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word right))) :
    evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_add_sat) =
      (some (.returned (.val (.word (wordAddSat left right)))),
        { emptyLocalsHOLFinite state with locals := (HolFiniteMapExact.resVarEq
          HolFiniteMapExact.empty (ofString "s", state.locals.lookup (ofString "s"))) }) := by
  classical
  have sa : ofString "s" ≠ ofString "a" := by decide_cbv
  have sb : ofString "s" ≠ ofString "b" := by decide_cbv
  rw [source_addSat_body, evaluateHOLFiniteState_dec_total]
  by_cases lower : (left + right).toNat < left.toNat
  all_goals have normalized := lower
  all_goals simp only [BitVec.toNat_add] at normalized
  all_goals simp [evalHOLExact, evalListHOLExact, toExact, ha, hb, shapeOfHOLExact,
    shapeEqHOL, wordOpHOL, wordOp, valueIsWord, valueWord,
    evaluateHOLFiniteState_seq, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
    setVarHOLFinite, FUPDATE, sa, sb, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    BitVec.lt_def, lower, normalized, Nat.not_le_of_lt, fixClockHOLFinite, emptyLocalsHOLFinite, wordAddSat]

  all_goals rfl

/-- Unsigned overflow detection implements natural saturated addition. -/
theorem wordAddSat_toNat (left right : BitVec 64) :
    (wordAddSat left right).toNat = min (left.toNat + right.toNat) (2^64 - 1) := by
  have hl := left.isLt
  have hr := right.isLt
  by_cases small : left.toNat + right.toNat < 2^64
  · have nlower : ¬(left + right).toNat < left.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt small]
      omega
    rw [wordAddSat, if_neg nlower, BitVec.toNat_add, Nat.mod_eq_of_lt small]
    omega
  · have reduced : (left.toNat + right.toNat) % 2^64 = left.toNat + right.toNat - 2^64 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have lower : (left + right).toNat < left.toNat := by
      rw [BitVec.toNat_add, reduced]
      omega
    simp only [wordAddSat, if_pos lower]
    change 18446744073709551615 = min (left.toNat + right.toNat) (2^64 - 1)
    omega

theorem wordAddSat_enough (left right amount : BitVec 64) :
    amount ≤ wordAddSat left right ↔ amount.toNat ≤ left.toNat + right.toNat := by
  rw [BitVec.le_def, wordAddSat_toNat]
  have bound := amount.isLt
  omega

def addSatCodeEntry : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=
  ([(ofString "a", .one), (ofString "b", .one)], sourceFunctionBody Guest.guestFn_add_sat, .one)

theorem lookup_source_addSat (code : MlS → Option
      (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (left right : BitVec 64) (installed : code (ofString "add_sat") = some addSatCodeEntry) :
    lookupCodeHOLFinite code (ofString "add_sat") [.val (.word left), .val (.word right)] =
      some (sourceFunctionBody Guest.guestFn_add_sat, minCalleeLocals left right, .one) := by
  apply lookupCodeFinite_of_exact
  have names : ofString "a" ≠ ofString "b" := by decide_cbv
  simp [lookupCodeHOLExact, installed, addSatCodeEntry, shapeOfHOLExact, shapeEqHOL, names]
  funext current
  by_cases hb : current = ofString "b"
  · subst current; simp [minCalleeLocals, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE]
  · by_cases ha : current = ofString "a"
    · subst current; simp [minCalleeLocals, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE, hb, Ne.symm hb]
    · simp [minCalleeLocals, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE, hb, ha, Ne.symm hb, Ne.symm ha]

/-- Executing the installed helper consumes exactly one source clock unit.
The continuation is left explicit so this summary applies to every caller. -/
theorem evaluate_addSat_decCall {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (left right : BitVec 64)
    (installed : state.code.lookup (ofString "add_sat") = some addSatCodeEntry)
    (args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word left), .val (.word right)])
    (clock : state.clock ≠ 0) :
    evaluateHOLFiniteState state (.decCall name .one (ofString "add_sat") arguments continuation) =
      let next := setVarHOLFinite name (.val (.word (wordAddSat left right)))
        { state with clock := state.clock - 1 }
      let output := evaluateHOLFiniteState next continuation
      (output.1, { output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
        (name, state.locals.lookup name)) }) := by
  classical
  have body := evaluate_source_addSat (callEntryStateHOLFinite state (minCalleeLocals left right))
    left right (minCalleeLocals_left left right) (minCalleeLocals_right left right)
  have noS : (minCalleeLocals left right).lookup (ofString "s") = none := by
    have sa : ofString "a" ≠ ofString "s" := by decide_cbv
    have sb : ofString "b" ≠ ofString "s" := by decide_cbv
    simp [minCalleeLocals, HolFiniteMapExact.update, HolFiniteMapExact.empty, FUPDATE, sa, sb]
  rw [evaluateHOLFiniteState_decCall_total, args]
  dsimp only
  rw [lookup_source_addSat state.code.lookup left right installed]
  simp only [clock, ↓reduceIte]
  rw [fixClockHOLFinite_evaluateState, body]
  simp [shapeOfHOLExact, shapeEqHOL, callEntryStateHOLFinite, emptyLocalsHOLFinite, noS, HolFiniteMapExact.resVarEq]

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.evaluate_source_addSat

#print axioms InitECandidate.Runtime.evaluate_addSat_decCall
