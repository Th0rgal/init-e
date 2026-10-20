import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.ZeroBytesWord
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- A normally returned real aligned memzero call establishes its zero-byte
coverage at any actual fuel. The existing forward proof is compared with
the same completed run plus enough clock, without a minimum-fuel premise. -/
theorem memzero_aligned_normal_zero_cells {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (destinationArgument sizeArgument : ExpHOL 64) (destination size : BitVec 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [destinationArgument,sizeArgument]=
  some [.val (.word destination),.val (.word size)])
 (code : s.code=originalRuntimeCode) (small : destination.toNat+size.toNat≤33806089496)
 (aligned : destination.toNat%8=0)
 (domain : ∀offset : Nat,offset<size.toNat→s.memaddrs (panByteAlignHOL (destination+BitVec.ofNat 64 offset)))
 (run : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "memzero") [destinationArgument,sizeArgument])=(none,post)) :
 ZeroBytePrefix post destination size.toNat := by
 have replay:=panPropsEvaluateAddClockEq (.call (some (none,none)) (ofString "memzero") [destinationArgument,sizeArgument]) s none post
  (size.toNat+1) ⟨run,by simp⟩
 let extended:={s with clock:=s.clock+(size.toNat+1)}
 have extendedArgs : evalListHOLFinite extended (h:=fun a=>Classical.propDecidable (extended.memaddrs a))
  [destinationArgument,sizeArgument]=some [.val (.word destination),.val (.word size)] := by
  rw [EvaluateClockSubCall.evalList_upd_clock]
  exact args
 obtain ⟨next,forward,covered,rest⟩:=evaluate_memzero_aligned_call_cells extended destinationArgument sizeArgument destination size extendedArgs code
  (by change size.toNat+1≤s.clock+(size.toNat+1);omega) small aligned domain
 have equal : next={post with clock:=post.clock+(size.toNat+1)} := (Prod.mk.inj (forward.symm.trans replay)).2
 rw [equal] at covered
 exact covered
#print axioms memzero_aligned_normal_zero_cells
end InitECandidate.Runtime
