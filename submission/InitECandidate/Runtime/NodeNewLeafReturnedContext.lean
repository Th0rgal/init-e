import InitECandidate.Runtime.NodeNewLeafBody
import InitECandidate.Runtime.HeapDeclarationReturnedContract
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The real leaf constructor's returned record and old-memory frame follow
from its actual allocation guards and stores. No caller reserve, successful
callee contract or minimum execution clock is assumed. -/
theorem node_new_leaf_returned_context {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (pointer nib length valuePointer valueLength : BitVec 64) (value : ValueHOL 64)
 (atNib : s.locals.lookup (ofString "nib")=some (.val (.word nib)))
 (atLength : s.locals.lookup (ofString "nlen")=some (.val (.word length)))
 (atValuePointer : s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (capped : pointer.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_new_leaf)=(some (.returned value),post)) :
 value=.val (.word pointer) ∧post.memory pointer=.word 1 ∧
 post.memory (pointer+32)=.word nib ∧post.memory (pointer+40)=.word length ∧
 post.memory (pointer+48)=.word valuePointer ∧post.memory (pointer+56)=.word valueLength ∧
 post.globals=s.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 64))) ∧
 pointer.toNat+64≤(allocationEnd pointer 64).toNat ∧
 (allocationEnd pointer 64).toNat≤33806089496 ∧(allocationEnd pointer 64).toNat%8=0 ∧
 (∀watched : BitVec 64,watched.toNat<pointer.toNat→post.memory watched=s.memory watched) ∧
 post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have metadata:=evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn_node_new_leaf)
 rw [run] at metadata
 rw [source_nodeNewLeaf_body] at run
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.const 64]=
  some [.val (.word (64#64))] := by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]
 obtain ⟨allocated,output,tailRun,scope,memory,domain,endian,installed,globals,request,finish⟩:=
  heap_declaration_returned_contract s post (ofString "nd") (.const 64) nodeNewLeafStores pointer 64 value args atHeap code run
 have extent:=allocationGuard_sum_bound pointer 64 capped request
 change pointer.toNat+64≤33806089496 at extent
 have covers:=allocationEnd_covers pointer 64 extent
 let ready:=setVarHOLFinite (ofString "nd") (.val (.word pointer)) {allocated with locals:=s.locals}
 have atRecord : ready.locals.lookup (ofString "nd")=some (.val (.word pointer)) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have other (name : MlS) (different : name≠ofString "nd") : ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
 have recordDomain : ∀offset∈([0,8,16,24,32,40,48,56] : List Nat),ready.memaddrs (pointer+BitVec.ofNat 64 offset) := by
  intro offset member
  have small : offset<64 := by simp at member;omega
  change allocated.memaddrs _
  rw [domain]
  apply fullDomain
  rw [BitVec.toNat_add,BitVec.toNat_ofNat]
  change (pointer.toNat+offset%2^64)%2^64<33806089496
  rw [Nat.mod_eq_of_lt (by omega : offset<2^64),Nat.mod_eq_of_lt (by omega)]
  omega
 have stores:=evaluate_nodeNewLeaf_stores ready pointer nib length valuePointer valueLength atRecord
  ((other _ (by decide)).trans atNib) ((other _ (by decide)).trans atLength)
  ((other _ (by decide)).trans atValuePointer) ((other _ (by decide)).trans atValueLength) recordDomain
 obtain ⟨returned,outputEq⟩:=Prod.mk.inj (tailRun.symm.trans stores)
 refine ⟨PanSemResultExact.returned.inj (Option.some.inj returned),?_,?_,?_,?_,?_,?_,covers.1,finish,covers.2.2,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [scope,outputEq]
   exact nodeNewLeafStoresPost_kind ready pointer nib length valuePointer valueLength
 · rw [scope,outputEq]
   simp [nodeNewLeafStoresPost,sourceWriteWord,emptyLocalsHOLFinite]
 · rw [scope,outputEq]
   simp [nodeNewLeafStoresPost,sourceWriteWord,emptyLocalsHOLFinite]
 · rw [scope,outputEq]
   simp [nodeNewLeafStoresPost,sourceWriteWord,emptyLocalsHOLFinite]
 · rw [scope,outputEq]
   simp [nodeNewLeafStoresPost,sourceWriteWord,emptyLocalsHOLFinite]
 · rw [scope,outputEq]
   exact globals
 · intro watched before
   rw [scope,outputEq]
   exact (nodeNewLeafStoresPost_before ready pointer nib length valuePointer valueLength extent watched before).trans
    (congrFun memory watched)

#print axioms node_new_leaf_returned_context
end InitECandidate.Runtime
