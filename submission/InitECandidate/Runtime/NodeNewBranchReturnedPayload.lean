import InitECandidate.Runtime.NodeNewBranchReturnedContext
import InitECandidate.Runtime.NodeNewBranchInitializePayload
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Actual successful original branch allocation and initialization establish
both zero payload words. Allocation extent and successful replay are derived
from the same returned run, with no room or minimum-clock assumption. -/
theorem node_new_branch_returned_payload {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (pointer : BitVec 64) (value : ValueHOL 64)
 (heap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (capped : pointer.toNat≤33806089496) (aligned : pointer.toNat%8=0)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_branch)=(some (.returned value),post)) :
 post.memory (pointer+160#64)=.word 0 ∧post.memory (pointer+168#64)=.word 0 := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.const 176]=
  some [.val (.word (176#64))] := by rw [evalListHOLFinite_eq_toExact];rfl
 have head:=run
 rw [source_nodeNewBranch_body] at head
 obtain ⟨allocationPost,output,tailRun,scope,memory,domain,endian,installed,globals,request,finish⟩:=
  heap_declaration_returned_contract s post (ofString "nd") (.const 176) nodeNewBranchInitialize pointer 176 value args heap code head
 have extent : pointer.toNat+176≤33806089496 := by
  have natural:=BitVec.le_def.mp request
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr capped)] at natural
  change 176≤33806089496-pointer.toNat at natural
  omega
 let ready:=setVarHOLFinite (ofString "nd") (.val (.word pointer)) {allocationPost with locals:=s.locals}
 change evaluateHOLFiniteState ready nodeNewBranchInitialize=(some (.returned value),output) at tailRun
 let lifted : PanSemStateFiniteExact 64 F:={ready with clock:=ready.clock+177}
 have sameRun : evaluateHOLFiniteState lifted nodeNewBranchInitialize=
  (some (.returned value),{output with clock:=output.clock+177}) :=
  panPropsEvaluateAddClockEq nodeNewBranchInitialize ready (some (.returned value)) output 177 ⟨tailRun,by simp⟩
 have address (offset : Nat) (small : offset<176) :
  (pointer+BitVec.ofNat 64 offset).toNat=pointer.toNat+offset := by
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  omega
 have payload:=node_new_branch_initialize_returned_payload lifted {output with clock:=output.clock+177} pointer value
  (by simp [lifted,ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  (installed.trans code) (by change 177≤ready.clock+177;omega) extent aligned
  (by intro offset small;change allocationPost.memaddrs _;rw [domain];exact fullDomain _ (by rw [address offset small];omega))
  (by intro offset small;change allocationPost.memaddrs _;rw [domain];apply fullDomain
      rw [panByteAlign_toNat64,address offset small]
      have := Nat.div_mul_le_self (pointer.toNat+offset) 8;omega)
  sameRun
 rw [scope]
 exact payload

#print axioms node_new_branch_returned_payload
end InitECandidate.Runtime
