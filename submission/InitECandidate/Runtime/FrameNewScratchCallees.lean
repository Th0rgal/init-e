import InitECandidate.Runtime.ComputeJumpdestsReturnedFrame
import InitECandidate.Runtime.ScratchListReturnedFrame
import InitECandidate.Runtime.ScratchHashReturnedFrame
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

inductive FrameNewScratchCallee where
 | bitmap (code length : BitVec 64)
 | logs
 | destruction

def FrameNewScratchCallee.function : FrameNewScratchCallee → MlS
 | .bitmap _ _=>ofString "compute_jumpdests" | .logs=>ofString "lst_new_scratch" | .destruction=>ofString "htab_new_scratch"
def FrameNewScratchCallee.firstName : FrameNewScratchCallee → MlS
 | .bitmap _ _=>ofString "code" | .logs=>ofString "esz" | .destruction=>ofString "key_len"
def FrameNewScratchCallee.secondName : FrameNewScratchCallee → MlS
 | .bitmap _ _=>ofString "n" | .logs | .destruction=>ofString "cap"
def FrameNewScratchCallee.firstWord : FrameNewScratchCallee → BitVec 64
 | .bitmap code _=>code | .logs=>8 | .destruction=>20
def FrameNewScratchCallee.secondWord : FrameNewScratchCallee → BitVec 64
 | .bitmap _ length=>length | .logs | .destruction=>4
def FrameNewScratchCallee.body : FrameNewScratchCallee → ProgHOL 64
 | .bitmap _ _=>sourceFunctionBody Guest.guestFn_compute_jumpdests
 | .logs=>sourceFunctionBody Guest.guestFn_lst_new_scratch
 | .destruction=>sourceFunctionBody Guest.guestFn_htab_new_scratch
def FrameNewScratchCallee.codeBound : FrameNewScratchCallee → Prop
 | .bitmap _ length=>length.toNat≤134217712 | _=>True

/-- A common physical endpoint for the THREE actual named frame_new scratch
constructors. This is a closed source-derived result, not an assumed callee
contract: the proof below checks each original complete function body. -/
theorem frame_new_actual_scratch_callee_returned {F : Type} (kind : FrameNewScratchCallee)
 (s post : PanSemStateFiniteExact 64 F) (scratch frame watched : BitVec 64) (value : ValueHOL 64)
 (firstLocal : s.locals.lookup kind.firstName=some (.val (.word kind.firstWord)))
 (secondLocal : s.locals.lookup kind.secondName=some (.val (.word kind.secondWord)))
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (ordered : frame≤scratch) (cap : scratch.toNat≤33806089496) (above : scratch.toNat≤watched.toNat)
 (code : s.code=originalRuntimeCode) (codeBound : kind.codeBound)
 (run : evaluateHOLFiniteState s kind.body=(some (.returned value),post)) :
 ∃pointer frontier : BitVec 64,value=.val (.word pointer) ∧
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word frontier)) ∧
 frame.toNat≤frontier.toNat ∧frontier.toNat≤pointer.toNat ∧pointer.toNat≤scratch.toNat ∧
 post.memory watched=s.memory watched ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have metadata:=evaluateHOLFiniteState_metadata s kind.body
 rw [run] at metadata
 cases kind with
 | bitmap source length=>
  obtain ⟨returned,memory,globals,lower,extent⟩:=compute_jumpdests_returned_upper_frame s post scratch frame length watched value
   scratchGlobal frameGlobal secondLocal ordered cap codeBound code above run
  let pointer:=scratchAllocationEnd scratch (computeJumpdestsBitmapSize length)
  change pointer.toNat+(computeJumpdestsBitmapSize length).toNat≤scratch.toNat at extent
  exact ⟨pointer,pointer,returned,globals,lower,Nat.le_refl _,by omega,memory,metadata.2.1,metadata.2.2.1,metadata.1⟩
 | logs=>
  obtain ⟨pointer,frontier,returned,globals,lower,dataExtent,recordExtent,memory,fields⟩:=scratch_list_8_4_returned_frame s post scratch frame watched value
   firstLocal secondLocal scratchGlobal frameGlobal ordered cap above code run
  exact ⟨pointer,frontier,returned,globals,lower,by omega,by omega,memory,metadata.2.1,metadata.2.2.1,metadata.1⟩
 | destruction=>
  obtain ⟨pointer,keys,vals,used,order,frontier,returned,globals,lower,orderPosExtent,orderExtent,usedExtent,valsExtent,keysExtent,tableExtent,memory⟩:=
   scratch_hash_20_4_returned_frame s post scratch frame watched value firstLocal secondLocal scratchGlobal frameGlobal ordered cap above code run
  exact ⟨pointer,frontier,returned,globals,lower,by omega,by omega,memory,metadata.2.1,metadata.2.2.1,metadata.1⟩
#print axioms frame_new_actual_scratch_callee_returned
end InitECandidate.Runtime
