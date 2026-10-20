import InitECandidate.Runtime.KeyToNibblesGeneralCallRange
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A completed actual conversion establishes nibble values at any clock.
Clock extension replays that same execution, so no fuel condition is added
to the later physical-memory invariant. -/
theorem key_to_nibbles_normal_range_any_clock {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (keyArgument sizeArgument outputArgument : ExpHOL 64) (key output length : BitVec 64)
 (small : 2*length.toNat+8<2^64) (code : s.code=originalRuntimeCode)
 (args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address))
  [keyArgument,sizeArgument,outputArgument]=some [.val (.word key),.val (.word length),.val (.word output)])
 (sourceDomain : ∀offset : Nat,offset<length.toNat→s.memaddrs (panByteAlignHOL (key+BitVec.ofNat 64 offset)))
 (outputDomain : ∀offset : Nat,offset<2*length.toNat→s.memaddrs (panByteAlignHOL (output+BitVec.ofNat 64 offset)))
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "key_to_nibbles")
  [keyArgument,sizeArgument,outputArgument])=(none,post)) :
 TrieNibbleRange post output (2*length) := by
 let extra:=length.toNat/4+4
 let extended:={s with clock:=s.clock+extra}
 have replay:=panPropsEvaluateAddClockEq
  (.call (some (none,none)) (ofString "key_to_nibbles") [keyArgument,sizeArgument,outputArgument])
  s none post extra ⟨run,by simp⟩
 have extendedArgs : evalListHOLFinite extended (h:=fun address=>Classical.propDecidable (extended.memaddrs address))
  [keyArgument,sizeArgument,outputArgument]=some [.val (.word key),.val (.word length),.val (.word output)] := by
  rw [EvaluateClockSubCall.evalList_upd_clock]
  exact args
 have facts:=evaluate_keyToNibbles_general_call_range extended keyArgument sizeArgument outputArgument key output length
  small code extendedArgs sourceDomain outputDomain (by change extra≤s.clock+extra;omega)
 rw [replay] at facts
 exact facts.2.2.2 rfl

#print axioms key_to_nibbles_normal_range_any_clock
end InitECandidate.Runtime
