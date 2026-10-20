import InitECandidate.Runtime.MemcpyGlobals
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual memcpy restores caller locals and keeps workspace and static state
at every actual normally completed fuel, without read/room/budget premises. -/
theorem memcpy_normal_state_metadata {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (arguments : List (ExpHOL 64)) (destination source size : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word destination),.val (.word source),.val (.word size)])
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "memcpy") arguments)=(none,post)) :
 post.locals=s.locals ∧post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=((HolFiniteMapExact.empty.update (ofString "dst",.val (.word destination))).update (ofString "src",.val (.word source))).update (ofString "n",.val (.word size))
 have installed : s.code.lookup (ofString "memcpy")=some ([(ofString "dst",.one),(ofString "src",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memcpy,.one):=by rw [code];exact originalRuntimeCode_memcpy_lookup
 have lookup:=pan_three_word_lookup s.code.lookup (ofString "memcpy") (ofString "dst") (ofString "src") (ofString "n") (sourceFunctionBody Guest.guestFn_memcpy) destination source size (by decide) (by decide) (by decide) installed
 obtain ⟨_,_,_,_,locals⟩:=evaluate_discard_normal_body s post (ofString "memcpy") arguments [.val (.word destination),.val (.word source),.val (.word size)] (sourceFunctionBody Guest.guestFn_memcpy) callee .one args lookup run
 have metadata:=evaluateHOLFiniteState_metadata s (.call (some (none,none)) (ofString "memcpy") arguments)
 rw [run] at metadata
 exact ⟨locals,memcpy_call_normal_globals s post arguments destination source size args code run,metadata.2.1,metadata.2.2.1,metadata.1⟩
#print axioms memcpy_normal_state_metadata
end InitECandidate.Runtime
