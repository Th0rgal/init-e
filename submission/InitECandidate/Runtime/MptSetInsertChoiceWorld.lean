import InitECandidate.Runtime.MptSetInsertDispatchBound
import InitECandidate.Runtime.MptInsertIndexedAssignmentWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptSetInsertChoice : ProgHOL 64 :=
 .ite mptSetDeleteCondition mptSetDeleteCall
  (.call (some (some (.local,ofString "root"),none)) (ofString "_mpt_insert_node") mptSetInsertArguments)

theorem source_mpt_set_insert_choice : mptSetAt 2=.seq mptSetInsertChoice (mptSetAt 3) := by
 rw [source_mpt_set_dispatch]
 rfl

/-- The actual indexed non-delete choice earns the installed insertion result
and enlarged world. The condition is evaluated from the real value locals. -/
theorem mpt_set_insert_choice_world {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (frontier node key length valuePointer valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (nodeValid : node=0 ∨node∈live)
 (atRoot : s.locals.lookup (ofString "root")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word valuePointer)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (pointerNonzero : valuePointer≠0#64) (lengthNonzero : valueLength≠0#64)
 (capacity : ∀node∈live,32≤size node) (recordsBefore : ∀node∈live,node.toNat+32≤key.toNat)
 (aligned : key.toNat%8=0) (keyExtent : key.toNat+length.toNat≤33806089496) (short : length.toNat≤18)
 (code : s.code=originalRuntimeCode) (budget : 19*((2^64+203)+1)+1≤s.clock)
 (run : evaluateHOLFiniteState s mptSetInsertChoice=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions newBranches : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "root")=some (.val (.word root)) ∧(root=0 ∨root∈larger) ∧live⊆larger ∧extensions⊆newExtensions ∧branches⊆newBranches ∧
 AllocatedTrieWorld post larger newExtensions newBranches newSize finish ∧
 TrieNodeKinds post larger newExtensions newBranches ∧TrieNodePaths post larger newExtensions newBranches newSize finish ∧
 TriePathBuffer post larger newSize key length finish ∧
 (∀other : MlS,other≠ofString "root"→post.locals.lookup other=s.locals.lookup other) := by
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) mptSetInsertArguments=
  some [.val (.word node),.val (.word key),.val (.word length),.val (.word (0#64)),.val (.word valuePointer),.val (.word valueLength)] := by
  simp [mptSetInsertArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atRoot,atKey,atValue,atValueLength]
 have condition : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) mptSetDeleteCondition=
  some (.val (.word (0#64))) := by
  simp [mptSetDeleteCondition,evalHOLExact,evalListHOLExact,atValue,atValueLength,pointerNonzero,lengthNonzero,
   Compiler.Encoders.Asm.wordCmpHOL,wordOpHOL,wordOp,valueIsWord,valueWord]
  rfl
 unfold mptSetInsertChoice at run
 rw [evaluateHOLFiniteState_ite,condition] at run
 change evaluateHOLFiniteState s
  (.call (some (some (.local,ofString "root"),none)) (ofString "_mpt_insert_node") mptSetInsertArguments)=(none,post) at run
 exact mpt_insert_indexed_assignment_world s post live extensions branches size mptSetInsertArguments (ofString "root")
  frontier node key length 0 valuePointer valueLength args world kinds paths keyPath fullDomain nodeValid (by simp)
  capacity recordsBefore aligned keyExtent short code budget run

#print axioms source_mpt_set_insert_choice
#print axioms mpt_set_insert_choice_world
end InitECandidate.Runtime
