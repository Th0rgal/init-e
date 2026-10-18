import InitECandidate.Runtime.TxScalarWordBodyBound
import InitECandidate.Runtime.TxScalarItemBodyAbove
import InitECandidate.Runtime.RlpItemBodyAbove
import InitECandidate.Runtime.PanDecCallReturnedGlobalMemoryClockScope
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem txScalarWord_body_returned_above {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92642 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_tx_scalar_word) = (some (.returned value),post)) (address : BitVec 64) (above : ceiling ≤ address.toNat) :
    post.memory address = state.memory address := by
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
  rw [source_txScalarWord_body] at run
  obtain ⟨parsed,bodyPost,ready,output,bodyRun,_,memory,globals,_,_,_,_,tail,restored⟩ := evaluate_decCall_returned_global_memory_clock_scope
    state post (ofString "f") (ofString "tx_scalar_item") (.comb [.one,.one]) (.comb [.one,.one])
    [.var .local (ofString "arr"),.var .local (ofString "i"),.var .local (ofString "maxb")]
    [.val (.word array),.val (.word index),.val (.word maximum)] (sourceFunctionBody Guest.guestFn_tx_scalar_item)
    txScalarWordAfterField callee value passedArgs lookup run
  have retained := txScalarItem_body_returned_above entry bodyPost pointer length scratch frame ceiling inputLimit args
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    (by change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1; omega) parsed bodyRun address above
  have supported : readOnlyMemory txScalarWordAfterField = true := by
    simp only [txScalarWordAfterField,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl
  have kept := evaluate_readOnly_memory txScalarWordAfterField supported (setVarHOLFinite (ofString "f") parsed ready)
  rw [tail] at kept
  rw [restored]
  change output.memory address = state.memory address
  change output.memory = ready.memory at kept
  rw [kept,memory]
  exact retained

#print axioms txScalarWord_body_returned_above
end InitECandidate.Runtime
