import InitECandidate.Runtime.HtabBlockInit
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
/-- Successful table construction frames old memory at any initial fuel. Clock
extension is used only to apply the existing concrete constructor contract. -/
theorem state_init_table_normal_memory_unfuelled {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (width capacity heap : BitVec 64) (bits : Nat)
 (code : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (aligned : heap.toNat%8=0) (capped : heap.toNat≤33806089496)
 (domain : ∀a : BitVec 64,a.toNat<33806089496→s.memaddrs a)
 (power : capacity.toNat=2^bits) (widthSmall : width.toNat<2^28)
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (ofString "htab_new") [.const width,.const capacity])=(none,post)) :
 post.locals.lookup name=some (.val (.word heap)) ∧HeapRel s.globals post.globals ∧
 (∀watched : BitVec 64,watched.toNat<heap.toNat→post.memory watched=s.memory watched) := by
 have lifted:=panPropsEvaluateAddClockEq _ s none post (capacity.toNat+14) ⟨run,by simp⟩
 let start:={s with clock:=s.clock+(capacity.toNat+14)}
 let finish:={post with clock:=post.clock+(capacity.toNat+14)}
 change evaluateHOLFiniteState start (.call (some (some (.local,name),none)) (ofString "htab_new") [.const width,.const capacity])=(none,finish) at lifted
 obtain ⟨keys,stride,used,values,order,orderPos,_,_,_,_,_,atName,_,memory,_,rel⟩:=
  htabNew_call_assignV start finish name width capacity heap bits code atHeap aligned capped
   (fun a _ _ hi=>domain a hi) power widthSmall (by change capacity.toNat+14≤s.clock+(capacity.toNat+14);omega) lifted
 exact ⟨atName,rel,memory⟩
#print axioms state_init_table_normal_memory_unfuelled
end InitECandidate.Runtime
