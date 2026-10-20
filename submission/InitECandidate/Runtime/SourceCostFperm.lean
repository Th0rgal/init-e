import InitECandidate.Runtime.SourceCostPanSimpCode
import InitECandidate.Runtime.SourceCostGlobalsInvariant
import Flapjack.Pancake.Proofs.PanGlobals.FpermCode
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! `pan_globals` renames the original entry to a fresh name (`fperm`). A
renamed run has exactly the same canonical events: no event mentions a
function name. -/

theorem fperm_call (f g : MlS) (info) (function : MlStringHOL) (arguments : List (ExpHOL 64)) :
    fpermHOL f g (.call info function arguments) =
      .call (simpMapInfo (fpermHOL f g) info) (fpermName f g function) arguments := by
  rcases info with _ | ⟨returns, _ | ⟨exception, handlerVar, handler⟩⟩ <;> simp [fpermHOL, simpMapInfo]

theorem fperm_lookup (f g : MlS) {F : Type} {s : PanSemStateFiniteExact 64 F} {function : MlStringHOL}
    {values : List (ValueHOL 64)} {body callee returnShape}
    (lookup : lookupCodeHOLFinite s.code.lookup function values = some (body, callee, returnShape)) :
    lookupCodeHOLFinite (fpermCodeHOL f g s.code).lookup (fpermName f g function) values =
      some (fpermHOL f g body, callee, returnShape) := by
  have h := lookupCodeFpermCodeHOL f g s.code function values
  simp only [lookupCodeCanonicalHOL] at h
  rw [h, lookup]; rfl

theorem fperm_run (f g : MlS) {F : Type} {s : PanSemStateFiniteExact 64 F} {p : ProgHOL 64} {r post ev}
    (run : StatementRun s p r post ev) :
    r ≠ some .error → ∀ C, C = fpermCodeHOL f g s.code →
      StatementRun { s with code := C } (fpermHOL f g p) r { post with code := C } ev := by
  induction run with
  | assignInvalid expr invalid => intro ok; exact absurd rfl ok
  | assignFailure expr => intro ok; exact absurd rfl ok
  | returnOversize expr size => intro ok; exact absurd rfl ok
  | returnFailure expr => intro ok; exact absurd rfl ok
  | raiseFailure expr => intro ok; exact absurd rfl ok
  | storeRejected dst src write => intro ok; exact absurd rfl ok
  | storeSourceFailure dst src => intro ok; exact absurd rfl ok
  | storeAddressFailure dst => intro ok; exact absurd rfl ok
  | store32Rejected dst src write => intro ok; exact absurd rfl ok
  | storeByteRejected dst src write => intro ok; exact absurd rfl ok
  | declareMismatch init mismatch => intro ok; exact absurd rfl ok
  | declareFailure init => intro ok; exact absurd rfl ok
  | callArgumentsFailure args => intro ok; exact absurd rfl ok
  | callLookupFailure args lookup => intro ok; exact absurd rfl ok
  | declareCallArgumentsFailure args => intro ok; exact absurd rfl ok
  | declareCallLookupFailure args lookup => intro ok; exact absurd rfl ok
  | declareCallRejectedReturn args lookup clock bodyRun shapeMismatch => intro ok; exact absurd rfl ok
  | iteInvalidGuard guard invalid => intro ok; exact absurd rfl ok
  | whileInvalidGuard guard invalid => intro ok; exact absurd rfl ok
  | whileMissingGuard guard => intro ok; exact absurd rfl ok
  | storeInvalidAddress dst invalid => intro ok; exact absurd rfl ok
  | store32InvalidAddress dst invalid => intro ok; exact absurd rfl ok
  | storeByteInvalidAddress dst invalid => intro ok; exact absurd rfl ok
  | store32InvalidValue dst src invalid => intro ok; exact absurd rfl ok
  | storeByteInvalidValue dst src invalid => intro ok; exact absurd rfl ok
  | primitiveInvalid args operation valid => intro ok; exact absurd rfl ok
  | primitiveRejected args operation => intro ok; exact absurd rfl ok
  | primitiveArgumentsFailure args => intro ok; exact absurd rfl ok
  | raiseUndeclared expr missing => intro ok; exact absurd rfl ok
  | raiseRejectedValue expr declared invalid => intro ok; exact absurd rfl ok
  | skip s => intro _ C _; simp only [fpermHOL]; exact .skip _
  | breakStmt s => intro _ C _; simp only [fpermHOL]; exact .breakStmt _
  | continueStmt s => intro _ C _; simp only [fpermHOL]; exact .continueStmt _
  | annotation => intro _ C _; simp only [fpermHOL]; exact .annotation
  | tickStep clock => intro _ C _; simp only [fpermHOL]; exact .tickStep clock
  | tickTimeout clock => intro _ C _; simp only [fpermHOL]; exact .tickTimeout clock
  | seqNext one two ihOne ihTwo =>
    intro ok C hC
    simp only [fpermHOL]
    exact .seqNext (ihOne (by simp) C hC) (ihTwo ok C (by rw [one.code_eq]; exact hC))
  | seqStop terminal one ihOne =>
    intro ok C hC
    simp only [fpermHOL]
    exact .seqStop terminal (ihOne ok C hC)
  | iteYes guard nonzero body ihBody =>
    intro ok C hC
    simp only [fpermHOL]
    exact .iteYes (simpCode_costed C guard) nonzero (ihBody ok C hC)
  | iteNo guard body ihBody =>
    intro ok C hC
    simp only [fpermHOL]
    exact .iteNo (simpCode_costed C guard) (ihBody ok C hC)
  | whileFalse guard => intro _ C _; simp only [fpermHOL]; exact .whileFalse (simpCode_costed C guard)
  | whileTimeout guard nonzero clock =>
    intro _ C _; simp only [fpermHOL]; exact .whileTimeout (simpCode_costed C guard) nonzero clock
  | whileNext guard nonzero clock one rest ihOne ihRest =>
    intro ok C hC
    have r1 := ihOne (by simp) C hC
    have r2 := ihRest ok C (by rw [one.code_eq]; exact hC)
    simp only [fpermHOL] at r2 ⊢
    exact .whileNext (simpCode_costed C guard) nonzero clock r1 r2
  | whileContinue guard nonzero clock one rest ihOne ihRest =>
    intro ok C hC
    have r1 := ihOne (by simp) C hC
    have r2 := ihRest ok C (by rw [one.code_eq]; exact hC)
    simp only [fpermHOL] at r2 ⊢
    exact .whileContinue (simpCode_costed C guard) nonzero clock r1 r2
  | whileBreak guard nonzero clock one ihOne =>
    intro ok C hC
    simp only [fpermHOL]
    exact .whileBreak (simpCode_costed C guard) nonzero clock (ihOne (by simp) C hC)
  | whilePropagate guard nonzero clock notBreak notContinue one ihOne =>
    intro ok C hC
    simp only [fpermHOL]
    exact .whilePropagate (simpCode_costed C guard) nonzero clock notBreak notContinue (ihOne ok C hC)
  | @assignValue s kind name expression value events expr valid =>
    intro _ C _
    have run' := StatementRun.assignValue (simpCode_costed C expr) (s := { s with code := C })
      (kind := kind) (name := name) valid
    rw [simpCode_setKvar] at run'
    simp only [fpermHOL]; exact run'
  | returnValue expr size => intro _ C _; simp only [fpermHOL]; exact .returnValue (simpCode_costed C expr) size
  | raiseValue expr declared shapeMatches size =>
    intro _ C _; simp only [fpermHOL]
    exact .raiseValue (simpCode_costed C expr) declared shapeMatches size
  | storeValue dst src write =>
    intro _ C _; simp only [fpermHOL]
    exact .storeValue (simpCode_costed C dst) (simpCode_costed C src) write
  | store32Value dst src write =>
    intro _ C _; simp only [fpermHOL]
    exact .store32Value (simpCode_costed C dst) (simpCode_costed C src) write
  | storeByteValue dst src write =>
    intro _ C _; simp only [fpermHOL]
    exact .storeByteValue (simpCode_costed C dst) (simpCode_costed C src) write
  | declareValue init shapeMatch bodyRun ih =>
    intro ok C hC
    simp only [fpermHOL]
    exact .declareValue (simpCode_costed C init) shapeMatch (ih ok C hC)
  | @primitiveValue s name operator arguments values value args operation valid =>
    intro _ C _
    have run' := StatementRun.primitiveValue ((PanSimp.evalListCodeUpd C s arguments).trans args)
      operation valid (s := { s with code := C })
    rw [simpCode_listEvents] at run'
    simp only [fpermHOL]; exact run'
  | @external s function configuration configurationLength array arrayLength result post run =>
    intro _ C _
    have run' := StatementRun.external (evaluateCodeUpd_ExtCall C s function configuration
      configurationLength array arrayLength result post run)
    rw [simpCode_external] at run'
    simp only [fpermHOL]; exact run'
  | @sharedLoad s operator kind name address result post run =>
    intro _ C _
    have run' := StatementRun.sharedLoad (evaluateCodeUpd_ShMemLoad C s operator kind name address
      result post run)
    rw [simpCode_sharedLoad] at run'
    simp only [fpermHOL]; exact run'
  | @sharedStore s operator address value result post run =>
    intro _ C _
    have run' := StatementRun.sharedStore (evaluateCodeUpd_ShMemStore C s operator address value
      result post run)
    rw [simpCode_sharedStore] at run'
    simp only [fpermHOL]; exact run'
  | @callDone s info function arguments values body callee returnShape bodyResult bodyPost
      bodyEvents result post args lookup clock bodyRun plan ihBody =>
    intro ok C hC
    have bodyOk : bodyResult ≠ some .error := by
      rintro rfl; rw [simpCode_plan_error] at plan; cases plan; exact ok rfl
    have args' := (PanSimp.evalListCodeUpd C s arguments).trans args
    have lookup' := fperm_lookup f g lookup
    rw [← hC] at lookup'
    have r1 := ihBody bodyOk C hC
    have run' := StatementRun.callDone args' lookup' clock r1
      (simpCode_plan_done C (simp_plan_map_done (fpermHOL f g) plan))
    rw [simpCode_listEvents, simpCode_callGlobal, callGlobalEvents_simpMapInfo] at run'
    rw [fperm_call]; exact run'
  | @callHandler s info function arguments values body callee returnShape bodyResult bodyPost
      bodyEvents handlerEntry handlerProgram handlerEvents result post args lookup clock bodyRun plan
      handlerRun ihBody ihHandler =>
    intro ok C hC
    have bodyOk : bodyResult ≠ some .error := by
      rintro rfl; rw [simpCode_plan_error] at plan; cases plan
    have args' := (PanSimp.evalListCodeUpd C s arguments).trans args
    have lookup' := fperm_lookup f g lookup
    rw [← hC] at lookup'
    have r1 := ihBody bodyOk C hC
    have entryCode : handlerEntry.code = s.code := by
      rw [simpCode_plan_handler_code plan, bodyRun.code_eq]; rfl
    have r2 := ihHandler ok C (by rw [entryCode]; exact hC)
    have run' := StatementRun.callHandler args' lookup' clock r1
      (simpCode_plan_handler C (simp_plan_map_handler (fpermHOL f g) plan).1) r2
    rw [simpCode_listEvents] at run'
    rw [fperm_call]; exact run'
  | @callTimeout s info function arguments values body callee returnShape args lookup clock =>
    intro _ C hC
    have args' := (PanSimp.evalListCodeUpd C s arguments).trans args
    have lookup' := fperm_lookup f g lookup
    rw [← hC] at lookup'
    have run' := StatementRun.callTimeout (info := simpMapInfo (fpermHOL f g) info) args' lookup' clock
    rw [simpCode_listEvents, simpCode_callGlobal, callGlobalEvents_simpMapInfo] at run'
    rw [fperm_call]; exact run'
  | @declareCallTimeout s name shape function arguments continuation values body callee returnShape
      args lookup clock =>
    intro _ C hC
    have args' := (PanSimp.evalListCodeUpd C s arguments).trans args
    have lookup' := fperm_lookup f g lookup
    rw [← hC] at lookup'
    have run' := StatementRun.declareCallTimeout (name := name) (shape := shape)
      (continuation := fpermHOL f g continuation) args' lookup' clock
    rw [simpCode_listEvents] at run'
    simp only [fpermHOL]; exact run'
  | @declareCallReturn s name shape function arguments continuation values body callee returnShape
      value bodyPost bodyEvents continuationEvents result post args lookup clock bodyRun shapeMatch
      continuationRun ihBody ihContinuation =>
    intro ok C hC
    have args' := (PanSimp.evalListCodeUpd C s arguments).trans args
    have lookup' := fperm_lookup f g lookup
    rw [← hC] at lookup'
    have r1 := ihBody (by simp) C hC
    have r2 := ihContinuation ok C
      (by show C = fpermCodeHOL f g bodyPost.code; rw [bodyRun.code_eq]; exact hC)
    have run' := StatementRun.declareCallReturn args' lookup' clock r1 shapeMatch r2
    rw [simpCode_listEvents] at run'
    simp only [fpermHOL]; exact run'
  | @declareCallStopped s name shape function arguments continuation values body callee returnShape
      bodyResult bodyPost bodyEvents args lookup clock bodyRun terminal ihBody =>
    intro ok C hC
    have bodyOk : bodyResult ≠ some .error := by
      rintro rfl; exact ok rfl
    have args' := (PanSimp.evalListCodeUpd C s arguments).trans args
    have lookup' := fperm_lookup f g lookup
    rw [← hC] at lookup'
    have r1 := ihBody bodyOk C hC
    have run' := StatementRun.declareCallStopped (name := name) (shape := shape)
      (continuation := fpermHOL f g continuation) args' lookup' clock r1 terminal
    rw [simpCode_stopPlan, simpCode_listEvents] at run'
    simp only [fpermHOL]; exact run'

#print axioms fperm_run
end InitECandidate.Runtime.FineCost
