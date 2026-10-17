import InitECandidate.Runtime.StateStorageHeaderFailure
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every terminal constructor exit on the missing-inner branch bypasses both
journal updates. This is independent of the allocation that failed. -/
theorem evaluate_storage_new_inner_terminal_constructor {F : Type}
    (state : PanSemStateFiniteExact 64 F) (lookupValue : BitVec 64)
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word (0 : BitVec 64)),.val (.word lookupValue)]))
    (terminal : (evaluateHOLFiniteState state (.call (some (some (.local,ofString "inner"),none)) (ofString "htab_new") [.const 32,.const 8])).1 ≠ none) :
    evaluateHOLFiniteState state stateStorageInnerSelection =
      evaluateHOLFiniteState state (.call (some (some (.local,ofString "inner"),none)) (ofString "htab_new") [.const 32,.const 8]) := by
  let constructor : ProgHOL 64 := .call (some (some (.local,ofString "inner"),none)) (ofString "htab_new") [.const 32,.const 8]
  let link : ProgHOL 64 := .call (some (none,none)) (ofString "jset")
    [.var .local (ofString "outer"),.var .local (ofString "addr"),.var .local (ofString "inner")]
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
  exact run

#print axioms evaluate_storage_new_inner_terminal_constructor
end InitECandidate.Runtime
