import InitECandidate.Runtime.StorageTableHeaderFailureCall
import InitECandidate.Runtime.StateStorageInnerSelection
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A terminal first component bypasses the complete continuation, retaining
both its exceptional result and its state. -/
theorem evaluate_seq_after_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (terminal : (evaluateHOLFiniteState state first).1 ≠ none) :
    evaluateHOLFiniteState state (.seq first second) = evaluateHOLFiniteState state first := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases output : evaluateHOLFiniteState state first with
  | mk result post =>
    rw [output] at terminal
    cases result with
    | none => exact False.elim (terminal rfl)
    | some result => rfl

/-- Header rejection on the original missing-inner branch skips both the
outer link and the value update, preserving its three-clock exceptional exit. -/
theorem evaluate_storage_new_inner_header_failure {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer lookupValue : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word (0 : BitVec 64)),.val (.word lookupValue)]))
    (rejected : ((33806089496 : BitVec 64) - pointer).toNat < 72) (ticks : 3 ≤ state.clock) :
    let output := evaluateHOLFiniteState state stateStorageInnerSelection;
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      output.2.clock = state.clock - 3 := by
  let constructor : ProgHOL 64 := .call (some (some (.local,ofString "inner"),none)) (ofString "htab_new") [.const 32,.const 8]
  let link : ProgHOL 64 := .call (some (none,none)) (ofString "jset")
    [.var .local (ofString "outer"),.var .local (ofString "addr"),.var .local (ofString "inner")]
  have failure := evaluate_storage_table_header_failure_call state pointer (some (.local,ofString "inner")) code heap rejected ticks
  have terminal : (evaluateHOLFiniteState state constructor).1 ≠ none := failure.1
  have innerRun := evaluate_seq_after_terminal state constructor link terminal
  have outerTerminal : (evaluateHOLFiniteState state (.seq constructor link)).1 ≠ none := by rw [innerRun]; exact terminal
  have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
    simp [evalHOLExact,mLocal,Compiler.Encoders.Asm.wordCmpHOL]
  have selected : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0)) (.seq constructor link)
        (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m"))))) =
      evaluateHOLFiniteState state (.seq constructor link) := by
    rw [evaluateHOLFiniteState_ite,condition]
    rfl
  have run : evaluateHOLFiniteState state stateStorageInnerSelection = evaluateHOLFiniteState state constructor := by
    change evaluateHOLFiniteState state (.seq
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0)) (.seq constructor link)
        (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m"))))) stateStorageValueTail) = _
    rw [evaluateHOLFiniteState_seq_line780,selected,innerRun]
    cases output : evaluateHOLFiniteState state constructor with
    | mk result post =>
      rw [output] at terminal
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result => rfl
  dsimp only
  rw [run]
  exact failure

/-- The enclosing declaration restores only locals, so the rejected header
still produces the same exceptional result and three-clock cost. -/
theorem evaluate_storage_new_inner_scope_header_failure {F : Type}
    (state : PanSemStateFiniteExact 64 F) (pointer lookupValue : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word (0 : BitVec 64)),.val (.word lookupValue)]))
    (rejected : ((33806089496 : BitVec 64) - pointer).toNat < 72) (ticks : 3 ≤ state.clock) :
    let output := evaluateHOLFiniteState state stateStorageInnerScope;
    output.1 ≠ none ∧ output.1 ≠ some .timeOut ∧ (∀ value, output.1 ≠ some (.returned value)) ∧
      output.2.clock = state.clock - 3 := by
  let entered := setVarHOLFinite (ofString "inner") (.val (.word (0 : BitVec 64))) state
  have atM : entered.locals.lookup (ofString "m") = some (.rStruct [.val (.word (0 : BitVec 64)),.val (.word lookupValue)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "inner" ≠ ofString "m" from by decide] using mLocal
  have failure := evaluate_storage_new_inner_header_failure entered pointer lookupValue code heap atM rejected ticks
  have full : evaluateHOLFiniteState state stateStorageInnerScope =
      (let output := evaluateHOLFiniteState entered stateStorageInnerSelection;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "inner",state.locals.lookup (ofString "inner"))})) := by
    unfold stateStorageInnerScope
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    rfl
  dsimp only
  rw [full]
  exact failure

#print axioms evaluate_storage_new_inner_scope_header_failure

#print axioms evaluate_seq_after_terminal
#print axioms evaluate_storage_new_inner_header_failure
end InitECandidate.Runtime
