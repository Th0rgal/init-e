import InitECandidate.Runtime.MptInsertLeafSource
import InitECandidate.Runtime.AllocatedTrieLeafFields
import InitECandidate.Runtime.HashWordStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def mptInsertLeafMatched : ProgHOL 64:=
 match mptInsertLeafEqualReturn with | .ite _ yes _=>yes | _=>.skip

theorem source_mpt_insert_leaf_equal_return : mptInsertLeafEqualReturn=
 .ite (.cmp .notEqual (.var .local (ofString "eq")) (.const 0)) mptInsertLeafMatched .skip :=rfl

theorem source_mpt_insert_leaf_matched : mptInsertLeafMatched=
 .seq (.store (.op .add [.var .local (ofString "node"),.const 48]) (.var .local (ofString "vptr")))
  (.seq (.store (.op .add [.var .local (ofString "node"),.const 56]) (.var .local (ofString "vlen")))
   (.return (.var .local (ofString "node")))) :=rfl

/-- Actual equal-key terminal leaf update. Allocated record extents earn both
store domains, exact kind tags protect the traversal registry, and the real
source returns the same live leaf without changing its heap frontier. -/
theorem evaluate_mpt_insert_leaf_matched_world {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier node value length : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches) (member : node∈live)
 (capacity : 64≤size node) (tag : s.memory node=.word (1#64))
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atLength : s.locals.lookup (ofString "vlen")=some (.val (.word length)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address) :
 ∃post,evaluateHOLFiniteState s mptInsertLeafMatched=(some (.returned (.val (.word node))),post) ∧
 AllocatedTrieWorld post live extensions branches size frontier ∧TrieNodeKinds post live extensions branches ∧
 post.memory (node+48)=.word value ∧post.memory (node+56)=.word length ∧
 post.globals=s.globals ∧post.clock=s.clock ∧
 (∀watched : BitVec 64,watched≠node+48→watched≠node+56→post.memory watched=s.memory watched) := by
 let first:=sourceWriteWord s (node+48#64) value
 let second:=sourceWriteWord first (node+56#64) length
 have domains (offset : Nat) (inside : offset<64) : s.memaddrs (node+BitVec.ofNat 64 offset) := by
  apply fullDomain
  rw [world.layout.field_nat node member offset (by omega)]
  have allocated:=world.allocated node member
  have capped:=world.capped
  omega
 have address (state : PanSemStateFiniteExact 64 F) (offset : Nat)
  (binding : state.locals.lookup (ofString "node")=some (.val (.word node))) :
  @evalHOLExact 64 F _ state.toExact (fun a=>Classical.propDecidable (state.memaddrs a))
   (.op .add [.var .local (ofString "node"),.const (BitVec.ofNat 64 offset)])=some (.val (.word (node+BitVec.ofNat 64 offset))) := by
  simp [evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord]
 have firstRun:=evaluate_store_word s (node+48#64) value _ (.var .local (ofString "vptr"))
  (address s 48 atNode) atValue (domains 48 (by decide))
 have secondRun:=evaluate_store_word first (node+56#64) length _ (.var .local (ofString "vlen"))
  (address first 56 atNode) atLength (domains 56 (by decide))
 have returned : evaluateHOLFiniteState second (.return (.var .local (ofString "node")))=
  (some (.returned (.val (.word node))),emptyLocalsHOLFinite second) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,second,first,sourceWriteWord,atNode,shapeOfHOLExact]
 obtain ⟨firstWorld,firstKinds⟩:=world.write_leaf_field kinds node value member capacity tag 48 (by decide) (by decide)
 have excluded:=kinds.leaf_separate node tag
 have firstTag : first.memory node=.word (1#64):=firstKinds.leaf node member excluded.1 excluded.2
 obtain ⟨secondWorld,secondKinds⟩:=firstWorld.write_leaf_field firstKinds node length member capacity firstTag 56 (by decide) (by decide)
 have different : node+48#64≠node+56#64 := by
  intro equal
  have impossible : (48#64)=(56#64):=add_left_cancel equal
  exact (by decide : (48#64)≠(56#64)) impossible
 refine ⟨emptyLocalsHOLFinite second,?_,secondWorld.after_memory_globals rfl rfl,?_,?_,?_,rfl,rfl,?_⟩
 · rw [source_mpt_insert_leaf_matched]
   exact evaluate_seq_none firstRun (evaluate_seq_none secondRun returned)
 · exact secondKinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro current registered;rfl)
 · change (sourceWriteWord first (node+56#64) length).memory (node+48#64)=_
   simp [sourceWriteWord,different,first]
 · change (sourceWriteWord first (node+56#64) length).memory (node+56#64)=_
   simp [sourceWriteWord]
 · intro watched n48 n56
   have a : watched≠node+48#64:=n48
   have b : watched≠node+56#64:=n56
   change second.memory watched=_
   simp [second,first,sourceWriteWord,a,b]

#print axioms evaluate_mpt_insert_leaf_matched_world
end InitECandidate.Runtime
