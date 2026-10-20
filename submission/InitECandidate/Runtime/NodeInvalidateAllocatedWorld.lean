import InitECandidate.Runtime.AllocatedTrieMetadata
import InitECandidate.Runtime.NodeInvalidateRegistry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_nodeInvalidate_allocated_world {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier pointer : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (member : pointer∈live) (capacity : 32≤size pointer)
 (binding : s.locals.lookup (ofString "nd")=some (.val (.word pointer)))
 (domain : ∀offset∈([8,16,24] : List Nat),s.memaddrs (pointer+BitVec.ofNat 64 offset)) :
 ∃post,evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_node_invalidate)=
  (some (.returned (.val (.word (0#64)))),post) ∧
 AllocatedTrieWorld post live extensions branches size frontier ∧post.clock=s.clock ∧post.globals=s.globals ∧
 (∀watched : BitVec 64,watched≠pointer+8 →watched≠pointer+16 →watched≠pointer+24 →post.memory watched=s.memory watched) := by
 let s1:=sourceWriteWord s (pointer+8#64) 0
 let s2:=sourceWriteWord s1 (pointer+16#64) 0
 let s3:=sourceWriteWord s2 (pointer+24#64) 0
 have address (current : PanSemStateFiniteExact 64 F) (offset : Nat)
  (binding : current.locals.lookup (ofString "nd")=some (.val (.word pointer))) :
  @evalHOLExact 64 F _ current.toExact (fun a=>Classical.propDecidable (current.memaddrs a))
   (nodeInvalidateAddress offset)=some (.val (.word (pointer+BitVec.ofNat 64 offset))) := by
  simp [nodeInvalidateAddress,evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord]
 have first:=evaluate_store_word s (pointer+8#64) 0 _ (.const 0) (address s 8 binding) rfl (domain 8 (by simp))
 have second:=evaluate_store_word s1 (pointer+16#64) 0 _ (.const 0) (address s1 16 binding) rfl (domain 16 (by simp))
 have third:=evaluate_store_word s2 (pointer+24#64) 0 _ (.const 0) (address s2 24 binding) rfl (domain 24 (by simp))
 have returned : evaluateHOLFiniteState s3 (.return (.const 0))=
  (some (.returned (.val (.word (0#64)))),emptyLocalsHOLFinite s3) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
 have w1 : AllocatedTrieWorld s1 live extensions branches size frontier:=world.write_metadata pointer 0 member capacity 8 (by decide) (by decide)
 have w2 : AllocatedTrieWorld s2 live extensions branches size frontier:=w1.write_metadata pointer 0 member capacity 16 (by decide) (by decide)
 have w3 : AllocatedTrieWorld s3 live extensions branches size frontier:=w2.write_metadata pointer 0 member capacity 24 (by decide) (by decide)
 refine ⟨emptyLocalsHOLFinite s3,?_,w3.after_memory_globals rfl rfl,rfl,rfl,?_⟩
 · rw [source_nodeInvalidate_body]
   exact evaluate_seq_none first (evaluate_seq_none second (evaluate_seq_none third returned))
 · intro watched n8 n16 n24
   have a : watched≠pointer+8#64:=n8
   have b : watched≠pointer+16#64:=n16
   have c : watched≠pointer+24#64:=n24
   simp [emptyLocalsHOLFinite,s3,s2,s1,sourceWriteWord,a,b,c]

#print axioms evaluate_nodeInvalidate_allocated_world
end InitECandidate.Runtime
