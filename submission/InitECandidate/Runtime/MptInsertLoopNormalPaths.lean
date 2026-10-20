import InitECandidate.Runtime.MptInsertRankedLoopPaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the entire original insertion loop retains the
committed enlarged trie world within nineteen complete iteration budgets. -/
theorem mpt_insert_indexed_loop_normal_paths {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier key length valuePointer valueLength : BitVec 64) (rank : Nat)
 (active : MptInsertPathsActive s live extensions branches size frontier key length valuePointer valueLength rank)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 19*((2^64+203)+1)≤s.clock)
 (run : evaluateHOLFiniteState s (.while mptInsertCondition mptInsertLoopStep)=(none,post)) :
 MptInsertTerminalPaths post live extensions branches key length := by
 obtain ⟨node,slot,level,root,a,b,c,d,e,f,g,h,inside,rankEq⟩:=active.active.path
 have rankBound : rank≤19:=by omega
 have enough : rank*((2^64+203)+1)≤s.clock:=
  (Nat.mul_le_mul_right ((2^64+203)+1) rankBound).trans budget
 have complete:=mpt_insert_ranked_loop_paths s live extensions branches size frontier key length valuePointer valueLength
  rank active capacity recordsBefore aligned keyExtent short code enough
 rw [run] at complete
 obtain ⟨finalRank,ranked,_,_⟩:=complete.2.2.2 rfl
 rcases ranked with ⟨_,_,terminal⟩ | next
 · exact terminal
 · obtain ⟨node,slot,level,root,atNode,atSlot,atLevel,atRoot,nodeValid,rootValid,typed,backlink,inside,rankEq⟩:=next.active.path
   exact ⟨root,live,extensions,branches,size,frontier,atRoot,rootValid,(fun _ h=>h),(fun _ h=>h),
    (fun _ h=>h),next.active.world,next.kinds,next.paths,next.keyPath⟩

#print axioms mpt_insert_indexed_loop_normal_paths
end InitECandidate.Runtime
