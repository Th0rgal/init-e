import InitECandidate.Runtime.TxScalarU256AfterFieldFrame
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.TxScalarU256BodyBound
import InitECandidate.Runtime.TxScalarItemBodyNamedGlobal
import InitECandidate.Runtime.RlpItemBodyNamedGlobal
import InitECandidate.Runtime.PanDecCallReturnedGlobalClockScope
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem txScalarU256_body_returned_named_global {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (watched : MlS) (different : ofString "scratch_ptr" ≠ watched)
    (array index maximum pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (maxLocal : state.locals.lookup (ofString "maxb") = some (.val (.word maximum)))
    (args : evalListHOLFinite (callEntryStateHOLFinite state (txScalarWordCallee array index maximum))
      (h := fun address => Classical.propDecidable (state.memaddrs address)) txScalarItemArguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92667 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_scalar_u256) = (some (.returned value),post)) :
    post.globals.lookup watched = state.globals.lookup watched := by
  let callee := txScalarWordCallee array index maximum
  let entry := callEntryStateHOLFinite state callee
  have passedArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "i"),.var .local (ofString "maxb")] =
      some [.val (.word array),.val (.word index),.val (.word maximum)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,maxLocal]
  have installed := originalRuntimeCode_txScalarItem_lookup
  rw [← code] at installed
  have lookup := pan_three_word_shape_lookup state.code.lookup (ofString "tx_scalar_item")
    (ofString "arr") (ofString "i") (ofString "maxb") (sourceFunctionBody Guest.guestFn_tx_scalar_item)
    (.comb [.one,.one]) array index maximum (by decide) (by decide) (by decide) installed
  rw [source_txScalarU256_body] at run
  obtain ⟨parsed,bodyPost,ready,output,bodyRun,_,globals,_,_,_,readyCode,tail,restored⟩ := evaluate_decCall_returned_global_clock_scope
    state post (ofString "f") (ofString "tx_scalar_item") (.comb [.one,.one]) (.comb [.one,.one])
    [.var .local (ofString "arr"),.var .local (ofString "i"),.var .local (ofString "maxb")]
    [.val (.word array),.val (.word index),.val (.word maximum)] (sourceFunctionBody Guest.guestFn_tx_scalar_item)
    txScalarU256AfterField callee value passedArgs lookup run
  have bodyCode := (evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_scalar_item)).1
  rw [bodyRun] at bodyCode
  have readyInstalled : ready.code = originalRuntimeCode := readyCode.trans (bodyCode.trans code)
  have retained := txScalarItem_body_returned_named_global entry bodyPost watched different pointer length scratch frame ceiling inputLimit args
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1; omega) parsed bodyRun
  have frame : ∀ watched : MlS, output.globals.lookup watched = bodyPost.globals.lookup watched := by
    intro watched
    have same := congrArg (fun g => g.lookup watched)
      (txScalarU256_after_field_frame (setVarHOLFinite (ofString "f") parsed ready) readyInstalled).2
    rw [tail] at same
    exact same.trans (congrArg (fun g => g.lookup watched) globals)
  rw [restored]
  exact (frame watched).trans retained

#print axioms txScalarU256_body_returned_named_global
end InitECandidate.Runtime
