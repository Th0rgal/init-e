import InitECandidate.Runtime.HtabOutsideFrame
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem state_init_storage_table_body_returned_memory {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (heap : BitVec 64) (value : ValueHOL 64) (code : s.code=originalRuntimeCode)
 (atWidth : s.locals.lookup (ofString "key_len")=some (.val (.word (32#64))))
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word (64#64))))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (aligned : heap.toNat%8=0) (capped : heap.toNat≤33806089496)
 (domain : ∀a : BitVec 64,a.toNat<33806089496→s.memaddrs a)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_htab_new)=(some (.returned value),post)) :
 value=.val (.word heap) ∧HeapRel s.globals post.globals ∧
 (∀watched : BitVec 64,watched.toNat<heap.toNat→post.memory watched=s.memory watched) := by
 have lifted:=panPropsEvaluateAddClockEq _ s (some (.returned value)) post 77 ⟨run,by simp⟩
 let start:={s with clock:=s.clock+77}
 let finish:={post with clock:=post.clock+77}
 change evaluateHOLFiniteState start (sourceFunctionBody Guest.guestFn_htab_new)=(some (.returned value),finish) at lifted
 obtain ⟨keys,stride,used,values,order,orderPos,returned,_,_,_,_,memory⟩:=htabNew_returned_frame start finish value
  32 64 heap 6 code atWidth atCapacity atHeap aligned capped (fun a _ _ hi=>domain a hi)
  (by decide) (by decide) (by decide) (by decide) (by change 77≤s.clock+77;omega) lifted
 have rel:=normalRel_apply htabNew_normalRel (X:=s)
  (by rw [run];exact Or.inr (Or.inr (Or.inr ⟨value,rfl⟩))) code
 rw [run] at rel
 exact ⟨returned,rel,memory⟩
#print axioms state_init_storage_table_body_returned_memory
end InitECandidate.Runtime
