import InitECandidate.Runtime.MptInsertBranchValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A successful actual node-field initializer supplies its own readability
and word value. This is used when inverting the real extension declarations,
rather than assuming domains of an intermediate prefix state. -/
theorem mpt_insert_node_load_word {F : Type} (s : PanSemStateFiniteExact 64 F)
 (node : BitVec 64) (offset : Nat) (value : ValueHOL 64)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.load .one (mptInsertNodeAddress offset))=some value) :
 ∃word : BitVec 64,value=.val (.word word) ∧
 s.memory (node+BitVec.ofNat 64 offset)=.word word ∧s.memaddrs (node+BitVec.ofNat 64 offset) := by
 have address : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (mptInsertNodeAddress offset)=some (.val (.word (node+BitVec.ofNat 64 offset))) := by
  simp [mptInsertNodeAddress,evalHOLExact,evalListHOLExact,atNode,wordOpHOL,wordOp,valueIsWord,valueWord]
 have load : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.load .one (mptInsertNodeAddress offset))=
  @memLoadHOLExact 64 _ .one (node+BitVec.ofNat 64 offset) s.memaddrs
   (fun a=>Classical.propDecidable (s.memaddrs a)) s.memory s.structs := by
  rw [evalHOLExact,address]
  rfl
 rw [load] at evaluated
 by_cases accessible : s.memaddrs (node+BitVec.ofNat 64 offset)
 · cases memory : s.memory (node+BitVec.ofNat 64 offset) with
   | word word=>
    have loaded : @memLoadHOLExact 64 _ .one (node+BitVec.ofNat 64 offset) s.memaddrs
     (fun a=>Classical.propDecidable (s.memaddrs a)) s.memory s.structs=some (.val (.word word)) := by
     simp [memLoadHOLExact,accessible,memory]
    exact ⟨word,Option.some.inj (evaluated.symm.trans loaded),rfl,accessible⟩
 · simp [memLoadHOLExact,accessible] at evaluated

#print axioms mpt_insert_node_load_word
end InitECandidate.Runtime
