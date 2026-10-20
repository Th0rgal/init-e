import InitECandidate.Runtime.MptInsertExtensionAdvance
import InitECandidate.Runtime.AllocatedTrieMetadata
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual successful extension advance itself proves the child-load
address is in the memory domain. No intermediate-prefix domain oracle is
needed when its normal run is available. -/
theorem mpt_insert_extension_advance_child_domain {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (node oldResult : BitVec 64)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (run : evaluateHOLFiniteState s mptInsertExtensionAdvance=(none,post)) :
 s.memaddrs (node+BitVec.ofNat 64 48) := by
 let ready:=setVarHOLFinite (ofString "r") (.val (.word node)) s
 have first:=evaluate_local_word_assignment s (ofString "r") (.var .local (ofString "node")) oldResult node atResult atNode
 rw [source_mptInsert_extension_advance,evaluateHOLFiniteState_seq_line780,first] at run
 dsimp only at run
 change evaluateHOLFiniteState ready (.seq (.assign .local (ofString "next_node")
  (.load .one (mptInsertNodeAddress 48))) _)=(none,post) at run
 by_contra missing
 have failed : @evalHOLExact 64 F _ ready.toExact (fun a=>Classical.propDecidable (ready.memaddrs a))
  (.load .one (mptInsertNodeAddress 48))=none := by
  simp (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
   mptInsertNodeAddress,evalHOLExact,evalListHOLExact,atNode,wordOpHOL,wordOp,valueIsWord,valueWord,
   isWfShapeExactHOL,memLoadHOLExact,missing]
  change @memLoadHOLExact 64 _ .one (node+BitVec.ofNat 64 48) s.memaddrs
   (fun a=>Classical.propDecidable (s.memaddrs a)) s.memory s.structs=none
  simp [memLoadHOLExact,missing]
 rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_assign,failed] at run
 cases run

/-- Same-run extension progress and concrete world preservation. Positive
length is earned from the indexed trie invariant, and the actual load guard
supplies readability after the prefix comparison. -/
theorem mpt_insert_extension_advance_normal_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (node level segment child keyLength oldResult oldNode oldSlot oldLevel oldGo : BitVec 64)
 (registered : node∈extensions)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atPrefix : s.locals.lookup (ofString "pl")=some (.val (.word segment)))
 (lengthField : s.memory (node+BitVec.ofNat 64 40)=.word segment)
 (childField : s.memory (node+BitVec.ofNat 64 48)=.word child)
 (fits : level.toNat+segment.toNat≤keyLength.toNat)
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (atNextNode : s.locals.lookup (ofString "next_node")=some (.val (.word oldNode)))
 (atNextSlot : s.locals.lookup (ofString "next_slot")=some (.val (.word oldSlot)))
 (atNextLevel : s.locals.lookup (ofString "next_level")=some (.val (.word oldLevel)))
 (atGo : s.locals.lookup (ofString "go")=some (.val (.word oldGo)))
 (run : evaluateHOLFiniteState s mptInsertExtensionAdvance=(none,post)) :
 AllocatedTrieWorld post live extensions branches size frontier ∧
 post.locals.lookup (ofString "r")=some (.val (.word node)) ∧
 post.locals.lookup (ofString "next_node")=some (.val (.word child)) ∧(child=0 ∨child∈live) ∧
 post.locals.lookup (ofString "next_slot")=some (.val (.word (node+BitVec.ofNat 64 48))) ∧
 post.locals.lookup (ofString "next_level")=some (.val (.word (level+segment))) ∧
 level.toNat<(level+segment).toNat ∧(level+segment).toNat≤keyLength.toNat ∧
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) ∧
 post.memory=s.memory ∧post.globals=s.globals := by
 have domain:=mpt_insert_extension_advance_child_domain s post node oldResult atNode atResult run
 obtain ⟨actualLength,loaded,positive⟩:=world.positive node registered
 have same : actualLength=segment:=HolWordLab.word.inj (loaded.symm.trans lengthField)
 subst actualLength
 obtain ⟨next,actualRun,result,nextNode,valid,nextSlot,typed,nextLevel,advanced,bounded,go,memory,clock⟩:=
  evaluate_mptInsert_extension_advance s live extensions branches world.registry node level segment child keyLength
   registered atNode atLevel atPrefix lengthField childField domain positive fits oldResult atResult oldNode atNextNode
   oldSlot atNextSlot oldLevel atNextLevel oldGo atGo
 have equal : next=post:=(Prod.mk.inj (actualRun.symm.trans run)).2
 subst next
 have globals:=evaluate_readOnly_globals mptInsertExtensionAdvance
  (by rw [source_mptInsert_extension_advance];rfl) s
 rw [run] at globals
 exact ⟨world.after_memory_globals memory globals,result,nextNode,valid,nextSlot,nextLevel,advanced,bounded,go,memory,globals⟩

#print axioms mpt_insert_extension_advance_child_domain
#print axioms mpt_insert_extension_advance_normal_world
end InitECandidate.Runtime
