import InitECandidate.Runtime.MptSetInsertDispatchBound
import InitECandidate.Runtime.TrieExternalWordStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual final mpt_set root store and return preserve the concrete trie
under explicit current-state header separation. Deriving that separation
from the repeated builder's allocations is a separate obligation. -/
theorem evaluate_mpt_set_root_store_world {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat) (frontier table root : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (external : TrieExternalWord s live branches table)
 (atTable : s.locals.lookup (ofString "m")=some (.val (.word table)))
 (atRoot : s.locals.lookup (ofString "root")=some (.val (.word root)))
 (domain : s.memaddrs table) :
 ∃post,evaluateHOLFiniteState s (mptSetAt 3)=(some (.returned (.val (.word (0#64)))),post) ∧
 post.memory table=.word root ∧AllocatedTrieWorld post live extensions branches size frontier ∧
 TrieNodeKinds post live extensions branches ∧TrieNodePaths post live extensions branches size frontier := by
 have address : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .add [.var .local (ofString "m"),.const 0])=some (.val (.word table)) := by
  simp [evalHOLExact,evalListHOLExact,atTable,wordOpHOL,wordOp,valueIsWord,valueWord]
 have store:=evaluate_store_word s table root (.op .add [.var .local (ofString "m"),.const 0])
  (.var .local (ofString "root")) address atRoot domain
 let stored:=sourceWriteWord s table root
 have returned : evaluateHOLFiniteState stored (.return (.const 0))=
  (some (.returned (.val (.word (0#64)))),emptyLocalsHOLFinite stored) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
 obtain ⟨worldOut,kindsOut,pathsOut⟩:=external.write_world_paths world kinds paths root
 refine ⟨emptyLocalsHOLFinite stored,?_,?_,worldOut.after_memory_globals rfl rfl,?_,pathsOut.after_context rfl rfl rfl⟩
 · rw [source_mpt_set_after_dispatch]
   exact evaluate_seq_none store returned
 · simp [stored,emptyLocalsHOLFinite,sourceWriteWord]
 · exact kindsOut.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;rfl)

#print axioms evaluate_mpt_set_root_store_world
end InitECandidate.Runtime
