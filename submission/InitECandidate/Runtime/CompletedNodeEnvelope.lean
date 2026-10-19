import InitECandidate.Runtime.ResolveStepBodyAlignedHeap
import InitECandidate.Runtime.DecodeStepReturnedHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def CompletedNodeEnvelope {F : Type} (s : PanSemStateFiniteExact 64 F) (node : BitVec 64) (floor : Nat) : Prop :=
  node=0 ∨ ∃ heap : BitVec 64,
    s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
    floor ≤ node.toNat ∧ node.toNat+32 ≤ heap.toNat ∧ heap.toNat ≤ 33806089496

theorem CompletedNodeEnvelope.after_globals {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (node : BitVec 64) (floor : Nat) (valid : CompletedNodeEnvelope s node floor)
    (globals : post.globals=s.globals) : CompletedNodeEnvelope post node floor := by
  rcases valid with zero | ⟨heap,atHeap,lower,upper,capped⟩
  · exact Or.inl zero
  · exact Or.inr ⟨heap,by rw [globals]; exact atHeap,lower,upper,capped⟩

theorem CompletedNodeEnvelope.lower_floor {F : Type} (s : PanSemStateFiniteExact 64 F)
    (node : BitVec 64) (floor lower : Nat) (valid : CompletedNodeEnvelope s node floor) (below : lower ≤ floor) :
    CompletedNodeEnvelope s node lower := by
  rcases valid with zero | ⟨heap,atHeap,starts,ends,capped⟩
  · exact Or.inl zero
  · exact Or.inr ⟨heap,atHeap,below.trans starts,ends,capped⟩

theorem returned_four_node_eq (node expected : BitVec 64) (flag len hash flag' len' hash' : ValueHOL 64)
    (same : ValueHOL.rStruct [flag,.val (.word node),len,hash] = .rStruct [flag',.val (.word expected),len',hash']) :
    node=expected := by
  exact HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj (List.cons.inj (ValueHOL.rStruct.inj same)).2).1)

theorem returned_four_tag_eq (flag expected : BitVec 64) (node len hash node' len' hash' : ValueHOL 64)
    (same : ValueHOL.rStruct [.val (.word flag),node,len,hash] = .rStruct [.val (.word expected),node',len',hash']) :
    flag=expected := by
  exact HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj (ValueHOL.rStruct.inj same)).1)

#print axioms CompletedNodeEnvelope.after_globals
#print axioms CompletedNodeEnvelope.lower_floor
#print axioms returned_four_node_eq
#print axioms returned_four_tag_eq
end InitECandidate.Runtime
