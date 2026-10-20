import InitECandidate.Runtime.MptNewEmptyReach
import InitECandidate.Runtime.HeapMarkDeclarationReach
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def buildMptIndexedAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_build_mpt_indexed)
theorem source_build_mpt_indexed_marker : sourceFunctionBody Guest.guestFn_build_mpt_indexed=
 .decCall (ofString "mark") .one (ofString "heap_mark") [] (buildMptIndexedAt 1) := by
 rw [sourceFunctionBody_eq_structural]
 rfl
theorem source_build_mpt_indexed_empty : buildMptIndexedAt 1=
 .decCall (ofString "m") .one (ofString "mpt_new") [.const 0,.const 0] (buildMptIndexedAt 2) := rfl

/-- The actual indexed-trie builder establishes a concrete empty trie and
its live-node registry before its insertion loop. The saved original heap
mark is retained. All constructor failures terminate in the same four clocks. -/
theorem build_mpt_indexed_empty_prefix_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (pointer : BitVec 64) (code : s.code=originalRuntimeCode)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (capped : pointer.toNat≤33806089496) (budget : 4≤s.clock) :
 Reaches s (sourceFunctionBody Guest.guestFn_build_mpt_indexed)
 (fun next=>∃marked : PanSemStateFiniteExact 64 F,HeapMarkDeclarationReady s (ofString "mark") pointer marked ∧
  MptNewEmptyReady marked next (ofString "m") pointer ∧
  next.locals.lookup (ofString "mark")=some (.val (.word pointer))) 4 (buildMptIndexedAt 2) := by
 have marker:=evaluate_heapMark_declaration_reaches s (ofString "mark") pointer (buildMptIndexedAt 1)
  code atHeap (by omega)
 rw [←source_build_mpt_indexed_marker] at marker
 refine reaches_trans_budget s _ (buildMptIndexedAt 1) (buildMptIndexedAt 2)
  (HeapMarkDeclarationReady s (ofString "mark") pointer) _ 1 3 budget marker ?_
 intro marked facts remaining
 have atMarkedHeap : marked.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)):=by
  rw [facts.2.2.1];exact atHeap
 have tree:=mpt_new_empty_declaration_reaches marked (ofString "m") pointer (buildMptIndexedAt 2)
  (facts.2.2.2.1.trans code) atMarkedHeap capped remaining
 rw [←source_build_mpt_indexed_empty] at tree
 refine reaches_mono marked (buildMptIndexedAt 1) (buildMptIndexedAt 2) _ _ 3 3 (le_refl _) ?_ tree
 intro next ready
 refine ⟨marked,facts,ready,?_⟩
 rw [ready.locals _ (by decide),facts.1]
 simp [HolFiniteMapExact.lookup_update,FUPDATE]
#print axioms source_build_mpt_indexed_marker
#print axioms source_build_mpt_indexed_empty
#print axioms build_mpt_indexed_empty_prefix_reaches
end InitECandidate.Runtime
