import InitECandidate.Runtime.RlpFinishListRuntimeBound
import InitECandidate.Runtime.OriginalRlpFinishListCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual list-finisher calls, with the real pointer difference as byte count. -/
theorem evaluate_rlp_finish_list_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64)) (dst payloadEnd : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word dst),.val (.word payloadEnd)])
 (code : s.code=originalRuntimeCode) (small : (payloadEnd-(dst+9#64)).toNat≤2^62)
 (budget : rlpFinishListSourceCost (payloadEnd-(dst+9#64)).toNat+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "rlp_finish_list") arguments)
  (rlpFinishListSourceCost (payloadEnd-(dst+9#64)).toNat+1) := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  (HolFiniteMapExact.empty.update (ofString "dst",.val (.word dst))).update (ofString "payload_end",.val (.word payloadEnd))
 let entry:=callEntryStateHOLFinite s callee
 have bounded:=rlp_finish_list_body_bounded entry dst payloadEnd
  (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) code small
  (by change rlpFinishListSourceCost (payloadEnd-(dst+9#64)).toNat≤s.clock-1;omega)
 have installed : s.code.lookup (ofString "rlp_finish_list")=
  some ([(ofString "dst",.one),(ofString "payload_end",.one)],sourceFunctionBody Guest.guestFn_rlp_finish_list,.one) := by
  rw [code];exact originalRuntimeCode_rlpFinishList_lookup
 have lookup:=pan_two_word_lookup s.code.lookup (ofString "rlp_finish_list") (ofString "dst") (ofString "payload_end")
  (sourceFunctionBody Guest.guestFn_rlp_finish_list) dst payloadEnd (by decide) installed
 unfold RunBounded at bounded
 cases ran : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_finish_list) with
 | mk result post=>
  rw [ran] at bounded
  have output:=evaluate_call_body_clock_no_timeout s post (ofString "rlp_finish_list") destination arguments
   [.val (.word dst),.val (.word payloadEnd)] (sourceFunctionBody Guest.guestFn_rlp_finish_list) callee .one
   result args lookup (by omega) ran bounded.2.2
  unfold RunBounded
  rw [output.2]
  have spent : s.clock-1≤post.clock+rlpFinishListSourceCost (payloadEnd-(dst+9#64)).toNat:=bounded.1
  have kept : post.clock≤s.clock-1:=bounded.2.1
  exact ⟨by omega,by omega,output.1⟩
#print axioms evaluate_rlp_finish_list_call_bounded
end InitECandidate.Runtime
