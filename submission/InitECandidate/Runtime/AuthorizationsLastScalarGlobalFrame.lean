import InitECandidate.Runtime.TxScalarU256InputGlobalFrame
import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.PanDecCallCheckedNormalMemoryScope
import InitECandidate.Runtime.TxScalarU256OuterPrefix
import InitECandidate.Runtime.FourWordValueShape
import InitECandidate.Runtime.AuthorizationsLastStorePrefix
import InitECandidate.Runtime.AuthorizationsTailSource
import InitECandidate.Runtime.TxScalarU256DeclarationInputBound
import InitECandidate.Runtime.TxScalarU256InputBound
import InitECandidate.Runtime.OriginalTxScalarU256Code
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.PanDecCallStraightBound
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful final scalar extraction and record completion preserve all globals. -/
theorem authorization_last_scalar_normal_global_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : 5 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668 ≤ state.clock)
    (run : evaluateHOLFiniteState state authorizationLastScalar = (none,post)) :
    ∀ watched : MlS, post.globals.lookup watched = state.globals.lookup watched := by
  let callee := txScalarWordCallee array 5 32
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word (5 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "maxb" ≠ ofString "i" by decide]
  have atMaximum : entry.locals.lookup (ofString "maxb") = some (.val (.word (32 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,txScalarWordCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have innerPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  have bodyBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92667 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92667 ≤ state.clock - 1
    omega
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "ent")),.const 5,.const 32] =
      some [.val (.word array),.val (.word (5 : BitVec 64)),.val (.word (32 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,entryLocal]
  have installed := originalRuntimeCode_txScalarU256_lookup
  rw [← code] at installed
  have lookup := pan_three_word_shape_lookup state.code.lookup (ofString "tx_scalar_u256")
    (ofString "arr") (ofString "i") (ofString "maxb") (sourceFunctionBody Guest.guestFn_tx_scalar_u256)
    (.comb [.one,.one,.one,.one]) array 5 32 (by decide) (by decide) (by decide) installed
  rw [source_authorization_last_scalar] at run
  obtain ⟨value,bodyPost,ready,output,bodyRun,checked,locals,memory,globals,clock,domain,endian,readyCode,tail,restored⟩ :=
    evaluate_decCall_checked_normal_memory_scope state post (ofString "s") (ofString "tx_scalar_u256")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_tx_scalar_u256) authorizationLastStore callee args lookup run
  have kept := txScalarU256_input_returned_global_frame entry bodyPost array 5 32 input inputLength scratch frame count
    ceiling inputLimit atArray atIndex atMaximum innerPrefix (by simpa using inside) inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget value bodyRun
  intro watched
  have supported : avoidsGlobalAssignment watched authorizationLastStore = true := by
    rw [source_authorization_last_store]
    rfl
  have finalSame := evaluate_avoidsGlobalAssignment watched authorizationLastStore supported
    (setVarHOLFinite (ofString "s") value ready)
  rw [tail] at finalSame
  rw [restored]
  exact finalSame.trans ((congrArg (fun g => g.lookup watched) globals).trans (kept watched))

#print axioms authorization_last_scalar_normal_global_frame
end InitECandidate.Runtime
