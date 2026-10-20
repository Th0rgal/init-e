import InitECandidate.Runtime.MemcpyCallMemory
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- An actual normally completed copy has its original concrete write frame
at any fuel; extending the same completed run removes the artificial budget. -/
theorem memcpy_normal_memory_any_clock {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (arguments : List (ExpHOL 64)) (destination source size watched : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word destination),.val (.word source),.val (.word size)])
 (code : s.code=originalRuntimeCode)
 (wordSeparate : ∀offset : Nat,offset<size.toNat → watched≠destination+BitVec.ofNat 64 offset)
 (byteSeparate : ∀offset : Nat,offset<size.toNat → watched≠panByteAlignHOL (destination+BitVec.ofNat 64 offset))
 (small : size.toNat≤33806089496)
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "memcpy") arguments)=(none,post)) :
 post.memory watched=s.memory watched := by
 let extra:=size.toNat/32+size.toNat/8+11
 let extended:={s with clock:=s.clock+extra}
 have replay:=panPropsEvaluateAddClockEq (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "memcpy") arguments) s none post extra ⟨run,by simp⟩
 have extendedArgs : evalListHOLFinite extended (h:=fun a=>Classical.propDecidable (extended.memaddrs a)) arguments=some [.val (.word destination),.val (.word source),.val (.word size)] := by rw [EvaluateClockSubCall.evalList_upd_clock];exact args
 exact memcpy_call_normal_memory extended {post with clock:=post.clock+extra} arguments destination source size watched extendedArgs code wordSeparate byteSeparate small (by change extra≤s.clock+extra;omega) replay
#print axioms memcpy_normal_memory_any_clock
end InitECandidate.Runtime
