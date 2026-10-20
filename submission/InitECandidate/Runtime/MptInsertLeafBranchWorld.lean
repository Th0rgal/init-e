import InitECandidate.Runtime.MptInsertLeafTailWorld
import InitECandidate.Runtime.CreateBranchTwoLeavesDeclarationWorld
import InitECandidate.Runtime.LocalWordFieldEval
import InitECandidate.Runtime.TriePayloadWords
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original divergent-leaf branch declaration and optional extension
return a live root with the complete allocated trie. Actual old payload
words follow from the memory datatype; their read domains follow from the
allocated leaf, without an extra typing or future-callee hypothesis. -/
theorem mpt_insert_leaf_branch_returned_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node oldKey oldLength key length matched value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (nodeLive : node∈live) (nonExt : node∉extensions) (nonBranch : node∉branches)
 (memoryKey : s.memory (node+32#64)=.word oldKey)
 (memoryLength : s.memory (node+40#64)=.word oldLength)
 (oldBound : matched.toNat≤oldLength.toNat) (newBound : matched.toNat≤length.toNat)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atOldKey : s.locals.lookup (ofString "ek")=some (.val (.word oldKey)))
 (atOldLength : s.locals.lookup (ofString "el")=some (.val (.word oldLength)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "rl")=some (.val (.word length)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 51≤s.clock) (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (mptInsertLeafAt 4)=(some (.returned returned),post)) :
 ∃root : BitVec 64,∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 returned=.val (.word root) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧
 AllocatedTrieWorld post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds post larger newExtensions (insert frontier branches) ∧
 TrieNodePaths post larger newExtensions (insert frontier branches) newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 obtain ⟨storedKey,storedLength,storedKeyAt,storedLengthAt,oldShort,oldPath⟩:=paths.paths node nodeLive nonBranch
 have oldKeyEq : storedKey=oldKey:=HolWordLab.word.inj (storedKeyAt.symm.trans memoryKey)
 have oldLengthEq : storedLength=oldLength:=HolWordLab.word.inj (storedLengthAt.symm.trans memoryLength)
 rw [oldKeyEq,oldLengthEq] at oldPath
 rw [oldLengthEq] at oldShort
 have oldSlice:=oldPath.suffix oldBound
 have newSlice:=keyPath.suffix newBound
 obtain ⟨oldValue,valueAt⟩:=source_memory_word s (node+48#64)
 obtain ⟨oldValueLength,valueLengthAt⟩:=source_memory_word s (node+56#64)
 have capacity:=paths.leafCapacity node nodeLive nonExt nonBranch
 have domain (offset : Nat) (small : offset<64) : s.memaddrs (node+BitVec.ofNat 64 offset) := by
  apply fullDomain
  rw [world.layout.field_nat node nodeLive offset (by omega)]
  have allocated:=world.allocated node nodeLive
  have capped:=world.capped
  omega
 have load48:=eval_local_word_field s (ofString "node") node 48 oldValue atNode (domain 48 (by decide)) valueAt
 have load56:=eval_local_word_field s (ofString "node") node 56 oldValueLength atNode (domain 56 (by decide)) valueLengthAt
 let arguments : List (ExpHOL 64):=
  [.op .add [.var .local (ofString "ek"),.var .local (ofString "pl")],
   .op .sub [.var .local (ofString "el"),.var .local (ofString "pl")],
   .load .one (.op .add [.var .local (ofString "node"),.const 48]),
   .load .one (.op .add [.var .local (ofString "node"),.const 56]),
   .op .add [.var .local (ofString "rk"),.var .local (ofString "pl")],
   .op .sub [.var .local (ofString "rl"),.var .local (ofString "pl")],
   .var .local (ofString "vptr"),.var .local (ofString "vlen")]
 have args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) arguments=
  some [.val (.word (oldKey+matched)),.val (.word (oldLength-matched)),.val (.word oldValue),.val (.word oldValueLength),
   .val (.word (key+matched)),.val (.word (length-matched)),.val (.word value),.val (.word valueLength)] := by
  simp [arguments,evalListHOLFinite,evalListHOLExact,load48,load56,evalHOLExact,atOldKey,atOldLength,atKey,atLength,
   atMatched,atValue,atValueLength,atNode,wordOpHOL,wordOp,valueIsWord,valueWord,
   isWfShapeExactHOL,memLoadHOLExact,domain 48 (by decide),domain 56 (by decide),valueAt,valueLengthAt]
 rw [source_mpt_insert_leaf_4] at run
 obtain ⟨ready,output,live2,size2,heap2,atBranch,locals,spent,clock,readyCode,readyDomain,readyEndian,sub2,
  world2,kinds2,paths2,transport2,tailRun,scope⟩:=create_branch_two_leaves_declaration_returned_world
   s post live extensions branches size frontier (oldKey+matched) (oldLength-matched) oldValue oldValueLength
   (key+matched) (length-matched) value valueLength world kinds paths oldSlice
   (by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr oldBound)];omega) newSlice
   (by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr newBound)];omega)
   (ofString "br") arguments (mptInsertLeafAt 5) args fullDomain code budget returned run
 obtain ⟨root,live3,extensions3,size3,heap3,returnedEq,rootLive,sub3,extSub,world3,kinds3,paths3,transport3⟩:=
  mpt_insert_leaf_tail_returned_world ready output live2 extensions (insert frontier branches) size2
   heap2 oldKey oldLength matched frontier world2 kinds2 paths2 (transport2 oldKey oldLength oldPath) oldShort oldBound
   (sub2 (Or.inl rfl)) ((locals _ (by decide)).trans atOldKey) ((locals _ (by decide)).trans atMatched) atBranch
   (by intro address small;rw [readyDomain];exact fullDomain address small) (readyCode.trans code) returned tailRun
 have memory : post.memory=output.memory:=by rw [scope]
 have globals : post.globals=output.globals:=by rw [scope]
 have domains : post.memaddrs=output.memaddrs:=by rw [scope]
 have endian : post.be=output.be:=by rw [scope]
 refine ⟨root,live3,extensions3,size3,heap3,returnedEq,rootLive,fun node member=>sub3 (sub2 (Or.inr member)),extSub,
  world3.after_memory_globals memory globals,?_,paths3.after_context memory domains endian,?_⟩
 · exact kinds3.after_kind_frame world3.layout.extensionLive world3.layout.branchLive (by intro node member;rw [memory])
 · intro nib len path
   exact (transport3 nib len (transport2 nib len path)).after_context memory domains endian

#print axioms mpt_insert_leaf_branch_returned_world
end InitECandidate.Runtime
