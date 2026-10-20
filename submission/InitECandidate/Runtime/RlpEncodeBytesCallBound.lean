import InitECandidate.Runtime.RlpEncodeBytesRuntimeBound
import InitECandidate.Runtime.PanThreeWordLookup
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Lift the concrete bounded byte encoder to actual calls with any result destination. -/
theorem evaluate_rlp_encode_bytes_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64)) (dst src length : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word dst),.val (.word src),.val (.word length)])
 (code : s.code=originalRuntimeCode) (small : length.toNat≤2^62)
 (budget : rlpEncodeBytesSourceCost length.toNat+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "rlp_encode_bytes") arguments)
  (rlpEncodeBytesSourceCost length.toNat+1) := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  ((HolFiniteMapExact.empty.update (ofString "dst",.val (.word dst))).update
   (ofString "src",.val (.word src))).update (ofString "n",.val (.word length))
 let entry:=callEntryStateHOLFinite s callee
 have bounded:=rlp_encode_bytes_body_bounded entry dst src length
  (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp (config:={decide:=true}) [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (by simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) code small
  (by change rlpEncodeBytesSourceCost length.toNat≤s.clock-1;omega)
 have installed : s.code.lookup (ofString "rlp_encode_bytes")=
  some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_encode_bytes,.one) := by
  rw [code];exact originalRuntimeCode_rlpEncodeBytes_lookup
 have lookup:=pan_three_word_lookup s.code.lookup (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
  (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) dst src length (by decide) (by decide) (by decide) installed
 unfold RunBounded at bounded
 cases ran : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) with
 | mk result post=>
  rw [ran] at bounded
  have output:=evaluate_call_body_clock_no_timeout s post (ofString "rlp_encode_bytes") destination arguments
   [.val (.word dst),.val (.word src),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) callee .one
   result args lookup (by omega) ran bounded.2.2
  unfold RunBounded
  rw [output.2]
  have spent : s.clock-1≤post.clock+rlpEncodeBytesSourceCost length.toNat:=bounded.1
  have kept : post.clock≤s.clock-1:=bounded.2.1
  exact ⟨by omega,by omega,output.1⟩
#print axioms evaluate_rlp_encode_bytes_call_bounded
end InitECandidate.Runtime
