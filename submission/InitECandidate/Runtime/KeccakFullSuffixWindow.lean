import InitECandidate.Runtime.KeccakMainLoopWindow
import InitECandidate.Runtime.KeccakMainLoopResult
import InitECandidate.Runtime.KeccakGeneralRemainderWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- After state zeroing, the full original hash preserves every watched word
outside its state, pad and output, including unsuccessful executions. -/
theorem keccak_full_after_zero_window {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output watched : BitVec 64)
    (atStp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atP : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (small : size.toNat ≤ 134217712)
    (code : state.code = originalRuntimeCode) (budget : size.toNat * 20 ≤ state.clock)
    (outsideState : ¬ MWin pointer 200 watched) (outsidePad : ¬ MWin pad 136 watched)
    (outsideOutput : ¬ MWin output 32 watched) :
    (evaluateHOLFiniteState state (stateInitSpineDrop 2 (sourceFunctionBody Guest.guestFn_keccak256))).2.memory watched =
      state.memory watched := by
  rw [source_keccak_after_state_zero]
  apply dec_watch
  intro v hv
  have value : v = .val (.word (0#64)) := by simpa [evalHOLExact] using hv.symm
  subst value
  let indexed := setVarHOLFinite (ofString "i") (.val (.word (0#64))) state
  have atI : indexed.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [indexed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have keep (key : MlS) (different : key ≠ ofString "i") : indexed.locals.lookup key = state.locals.lookup key := by
    simp [indexed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have n := (keep _ (by decide)).trans atN
  have p := (keep _ (by decide)).trans atP
  have stp := (keep _ (by decide)).trans atStp
  have frame := keccak_main_loop_window indexed pointer source 0 watched code stp p atI outsideState
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState indexed keccakMainLoop with
  | mk result next =>
    rw [loopRun] at frame
    cases result with
    | some r => exact frame
    | none =>
      obtain ⟨⟨index,idx,inside,aligned,tailSmall⟩,globals,installed,domain,kept⟩ :=
        keccak_main_loop_normal_result indexed next pointer source size code atI n p stp small budget loopRun
      have atN' := (kept _ (by decide)).trans n
      have remainderNat : (size - index).toNat = size.toNat - index.toNat :=
        BitVec.toNat_sub_of_le (BitVec.le_def.mpr inside)
      have tailFrame : (evaluateHOLFiniteState next keccakRemainderScope).2.memory watched = next.memory watched := by
        rw [source_keccak_remainder_scope]
        apply dec_watch
        intro rem ev
        have value : rem = .val (.word (size - index)) := by
          simpa [evalHOLExact,evalListHOLExact,atN',idx,wordOpHOL,wordOp,valueIsWord,valueWord] using ev.symm
        subst value
        let entered := setVarHOLFinite (ofString "rem") (.val (.word (size - index))) next
        have old (key : MlS) (different : key ≠ ofString "rem") : entered.locals.lookup key = next.locals.lookup key := by
          simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
        exact keccak_general_remainder_window entered source index (size - index) output pointer pad watched
          (installed.trans code) ((old _ (by decide)).trans ((kept _ (by decide)).trans p))
          ((old _ (by decide)).trans idx)
          (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
          ((old _ (by decide)).trans ((kept _ (by decide)).trans ((keep _ (by decide)).trans atOut)))
          ((old _ (by decide)).trans ((kept _ (by decide)).trans stp))
          (by change next.globals.lookup _ = _; rw [globals]; exact atPad)
          (by rw [remainderNat]; exact tailSmall) outsideState outsidePad outsideOutput
      exact tailFrame.trans frame

#print axioms keccak_full_after_zero_window
end InitECandidate.Runtime
