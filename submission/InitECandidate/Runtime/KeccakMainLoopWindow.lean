import InitECandidate.Runtime.DiscardCallSuccessLocals
import InitECandidate.Runtime.KeccakMainLoopBound
import InitECandidate.Runtime.KeccakWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def KeccakLoopWindowInv {F : Type} (pointer source : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Prop :=
  state.code = originalRuntimeCode ∧
  state.locals.lookup (ofString "stp") = some (.val (.word pointer)) ∧
  state.locals.lookup (ofString "p") = some (.val (.word source)) ∧
  ∃ index : BitVec 64, state.locals.lookup (ofString "i") = some (.val (.word index))

/-- Full-block Keccak absorption writes only its 200-byte state, at every fuel
and for every FFI outcome. This memory frame does not require an input-size bound. -/
theorem keccak_main_loop_window {F : Type} (state : PanSemStateFiniteExact 64 F) (pointer source index watched : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (atStp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atP : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (atI : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (outside : ¬ MWin pointer 200 watched) :
    (evaluateHOLFiniteState state keccakMainLoop).2.memory watched = state.memory watched := by
  rw [source_keccak_main_loop]
  apply (evaluate_while_watch keccakFullCondition keccakMainLoopBody watched (KeccakLoopWindowInv pointer source) ?_
    state ⟨code,atStp,atP,index,atI⟩).1
  intro current ⟨code,stp,p,index,idx⟩ value condition active
  let entered := decClockHOLFinite current
  have args : evalListHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a)) keccakFullArguments =
      some [.val (.word pointer),.val (.word (source + index))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [entered,decClockHOLFinite,keccakFullArguments,evalListHOLExact,evalHOLExact,stp,p,idx,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := (HolFiniteMapExact.empty.update (ofString "stp",.val (.word pointer))).update
    (ofString "blk",.val (.word (source + index)))
  have lookup := pan_two_word_lookup entered.code.lookup (ofString "keccak_absorb_block") (ofString "stp") (ofString "blk")
    (sourceFunctionBody Guest.guestFn_keccak_absorb_block) pointer (source + index) (by decide)
    (by rw [show entered.code = originalRuntimeCode from code]; exact originalRuntimeCode_keccakAbsorb_lookup)
  have bodyFrame := keccakAbsorb_body_window (callEntryStateHOLFinite entered callee) pointer (source + index) watched code
    (by simp (config := {decide := true}) [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) outside
  have bodyGlobals := keccakAbsorb_body_globals_frame (callEntryStateHOLFinite entered callee) code
  have firstFrame := watch_discardCall entered watched (ofString "keccak_absorb_block") keccakFullArguments
    [.val (.word pointer),.val (.word (source + index))] args _ callee .one lookup ⟨bodyFrame,bodyGlobals⟩
  have controls := evaluate_discard_call_no_loop_control entered (ofString "keccak_absorb_block") keccakFullArguments
  have metadata := evaluateHOLFiniteState_metadata entered
    (.call (some (none,none)) (ofString "keccak_absorb_block") keccakFullArguments)
  rw [source_keccak_main_body,evaluateHOLFiniteState_seq_line780]
  cases firstRun : evaluateHOLFiniteState entered (.call (some (none,none)) (ofString "keccak_absorb_block") keccakFullArguments) with
  | mk result middle =>
    rw [firstRun] at firstFrame controls metadata
    cases result with
    | none =>
      have locals := evaluate_discard_call_success_locals entered (ofString "keccak_absorb_block") keccakFullArguments
        (by rw [firstRun])
      rw [firstRun] at locals
      have midI : middle.locals.lookup (ofString "i") = some (.val (.word index)) := by rw [locals]; exact idx
      have midStp : middle.locals.lookup (ofString "stp") = some (.val (.word pointer)) := by rw [locals]; exact stp
      have midP : middle.locals.lookup (ofString "p") = some (.val (.word source)) := by rw [locals]; exact p
      have assign := evaluate_local_word_assignment middle (ofString "i")
        (.op .add [.var .local (ofString "i"),.const 136]) index (index + (136#64)) midI
        (by simp [evalHOLExact,evalListHOLExact,midI,wordOpHOL,wordOp,valueIsWord,valueWord])
      dsimp only
      rw [assign]
      refine ⟨firstFrame.1,fun _ => ⟨metadata.1.trans code,?_,?_,index + (136#64),?_⟩⟩
      · simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using midStp
      · simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using midP
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    | some result =>
      exact ⟨firstFrame.1,fun h => by rcases h with h | h | h; cases h; exact False.elim (controls.2 h); exact False.elim (controls.1 h)⟩

#print axioms keccak_main_loop_window
end InitECandidate.Runtime
