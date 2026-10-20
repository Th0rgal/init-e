import InitECandidate.Runtime.NodeNewBranchBody
import InitECandidate.Runtime.HeapDeclarationReturnedContract
import InitECandidate.Runtime.AllocationAligned
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A returned execution of the real constructor supplies its own allocation
extent. Replaying that same completed initializer with extra clocks derives
the zero children, kind and old-memory frame without a caller room premise. -/
theorem node_new_branch_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (pointer : BitVec 64) (value : ValueHOL 64)
 (heap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (capped : pointer.toNat≤33806089496) (aligned : pointer.toNat%8=0)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_branch)=(some (.returned value),post)) :
 value=.val (.word pointer) ∧ post.memory pointer=.word 3 ∧
 (∀slot : Nat,slot<16→post.memory (branchChildAddress pointer slot)=.word 0) ∧
 post.globals=s.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 176))) ∧
 pointer.toNat+176≤(allocationEnd pointer 176).toNat ∧ (allocationEnd pointer 176).toNat≤33806089496 ∧
 (allocationEnd pointer 176).toNat%8=0 ∧
 (∀watched : BitVec 64,watched.toNat<pointer.toNat→post.memory watched=s.memory watched) ∧
 post.memaddrs=s.memaddrs ∧ post.be=s.be ∧ post.code=s.code := by
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
 obtain ⟨replayed,replay,_,_,kind,children,keptGlobals,_,_,_,before⟩:=
  evaluate_nodeNewBranch_initialize lifted pointer
   (by simp [lifted,ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (installed.trans code) (by change 177≤ready.clock+177;omega) extent aligned
   (by intro offset small;change allocationPost.memaddrs _;rw [domain];exact fullDomain _ (by rw [address offset small];omega))
   (by intro offset small;change allocationPost.memaddrs _;rw [domain];apply fullDomain
       rw [panByteAlign_toNat64,address offset small]
       have := Nat.div_mul_le_self (pointer.toNat+offset) 8;omega)
 rw [sameRun] at replay
 have returned := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj replay).1)
 have postEq := (Prod.mk.inj replay).2
 rw [←postEq] at kind children keptGlobals before
 have metadata:=evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn_node_new_branch)
 rw [run,scope] at metadata
 rw [scope]
 refine ⟨returned,kind,children,keptGlobals.trans globals,?_,finish,?_,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · exact (allocationEnd_covers pointer 176 extent).1
 · exact (allocationEnd_covers pointer 176 extent).2.2
 · intro watched lower
   exact (before watched lower).trans (congrFun memory watched)

#print axioms node_new_branch_returned_context
end InitECandidate.Runtime
