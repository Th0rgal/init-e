import InitECandidate.Runtime.VersionedHashesScanReadFrame
import InitECandidate.Runtime.VersionedHashesTypedScanCallBound
import InitECandidate.Runtime.PanDecCallNormalWordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem versioned_hashes_typed_scan_normal_read_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx vh cursor : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.decCall (ofString "isb") .one (ofString "tx_is_blob")
      [.var .local (ofString "tx")] versionedHashesScanTail) = (none,post)) :
    post.memory = state.memory ∧ post.globals = state.globals := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "tx",.val (.word tx))
  have lookup := pan_single_word_lookup state.code.lookup (ofString "tx_is_blob") (ofString "tx")
    (sourceFunctionBody Guest.guestFn_tx_is_blob) tx (by rw [code]; exact originalRuntimeCode_txIsBlob_lookup)
  have bodyRead : readOnlyMemory (sourceFunctionBody Guest.guestFn_tx_is_blob) = true := by
    simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl
  obtain ⟨word,ready,output,locals,memory,globals,domain,readyCode,tailRun,scope⟩ :=
    evaluate_decCall_one_normal_word_frame state post (ofString "isb") (ofString "tx_is_blob")
      [.var .local (ofString "tx")] [.val (.word tx)] (sourceFunctionBody Guest.guestFn_tx_is_blob)
      versionedHashesScanTail callee
      (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,txLocal]) lookup
      (by intro result final bodyRun
          have mem := evaluate_readOnly_memory _ bodyRead (callEntryStateHOLFinite state callee)
          have glob := evaluate_readOnly_globals _ bodyRead (callEntryStateHOLFinite state callee)
          rw [bodyRun] at mem glob
          exact ⟨mem,glob⟩) run
  let resumed := setVarHOLFinite (ofString "isb") (.val (.word word)) ready
  have atTx : resumed.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "isb" ≠ ofString "tx" by decide] using txLocal
  have atVh : resumed.locals.lookup (ofString "vh") = some (.val (.word vh)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "isb" ≠ ofString "vh" by decide] using vhLocal
  have atK : resumed.locals.lookup (ofString "k") = some (.val (.word cursor)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "isb" ≠ ofString "k" by decide] using cursorLocal
  change evaluateHOLFiniteState resumed versionedHashesScanTail = (none,output) at tailRun
  unfold versionedHashesScanTail at tailRun
  rw [evaluateHOLFiniteState_seq_line780] at tailRun
  cases scanned : evaluateHOLFiniteState resumed versionedHashesScan with
  | mk result middle =>
    rw [scanned] at tailRun
    cases result with
    | some result => cases tailRun
    | none =>
      dsimp only at tailRun
      have frame := versioned_hashes_scan_normal_read_frame resumed middle tx vh cursor atTx atVh atK (readyCode.trans code) scanned
      have mem := evaluate_readOnly_memory (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) (by rfl) middle
      have glob := evaluate_readOnly_globals (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) (by rfl) middle
      rw [tailRun] at mem glob
      rw [scope]
      exact ⟨mem.trans (frame.1.trans memory),glob.trans (frame.2.trans globals)⟩

#print axioms versioned_hashes_typed_scan_normal_read_frame
end InitECandidate.Runtime
