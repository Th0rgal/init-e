import InitECandidate.Runtime.SplitExtensionSingleChildWorld
import InitECandidate.Runtime.SplitExtensionLongChildWorld
import InitECandidate.Runtime.SplitExtensionIncomingDeclarationWorld
import InitECandidate.Runtime.SplitExtensionArmsBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete actual post-allocation split tail, including both old-child
arms, incoming suffix declaration, collision rejection, leaf/payload and return. -/
theorem split_extension_children_returned_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier branch segment segmentLength key length matched oldSuffix child value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (segmentPath : TriePathBuffer s live size segment segmentLength frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (shortSegment : segmentLength.toNat≤18) (shortKey : length.toNat≤18)
 (inside : matched.toNat<segmentLength.toNat) (matchedBound : matched.toNat≤length.toNat)
 (oldSuffixEq : oldSuffix=segmentLength-matched)
 (member : branch∈branches) (childValid : child=0∨child∈live)
 (atBranch : s.locals.lookup (ofString "br")=some (.val (.word branch)))
 (atSegment : s.locals.lookup (ofString "seg")=some (.val (.word segment)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atSuffix : s.locals.lookup (ofString "sal")=some (.val (.word oldSuffix)))
 (atChild : s.locals.lookup (ofString "child")=some (.val (.word child)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "rl")=some (.val (.word length)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 7≤s.clock)
 (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (splitExtensionAt 5)=(some (.returned returned),post)) :
 returned=.val (.word branch) ∧
 ∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 live⊆larger ∧extensions⊆newExtensions ∧AllocatedTrieWorld post larger newExtensions branches newSize finish ∧
 TrieNodeKinds post larger newExtensions branches ∧TrieNodePaths post larger newExtensions branches newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 rw [source_split_extension_5,source_split_extension_6] at run
 obtain ⟨middle,firstRun,remaining⟩:=seq_returned_of_nonreturning_first
  (fun value=>evaluate_noTopReturn splitExtensionSingleChild rfl s value) run
 obtain ⟨world1,kinds1,paths1,transport1⟩:=split_extension_single_child_normal_world s middle live extensions branches size
  frontier branch segment segmentLength matched oldSuffix child world kinds paths segmentPath inside member childValid
  atBranch atSegment atMatched atSuffix atChild fullDomain firstRun
 have firstLocals : middle.locals=s.locals := by
  apply HolFiniteMapExact.ext;funext name
  have kept:=evaluate_avoidsLocal_flowing name splitExtensionSingleChild
   (by simp [splitExtensionSingleChild,branchNibbleStore,avoidsLocal]) s
  rw [firstRun] at kept;exact kept (Or.inl rfl)
 have firstMetadata:=evaluateHOLFiniteState_metadata s splitExtensionSingleChild
 rw [firstRun] at firstMetadata
 have middleCode : middle.code=originalRuntimeCode:=firstMetadata.1.trans code
 have middleDomain : ∀address : BitVec 64,address.toNat<33806089496→ middle.memaddrs address:=by
  intro address small;rw [firstMetadata.2.1];exact fullDomain address small
 have firstCount:=RunBounded.ofProg split_extension_single_child_bounded code (Nat.zero_le s.clock)
 unfold RunBounded at firstCount;rw [firstRun] at firstCount;dsimp only at firstCount
 have middleBudget : 7≤middle.clock:=by omega
 obtain ⟨lastState,secondRun,tailRun⟩:=seq_returned_of_nonreturning_first
  (fun value=>evaluate_noTopReturn splitExtensionLongChild rfl middle value) remaining
 obtain ⟨live2,extensions2,size2,heap2,sub2,ext2,world2,kinds2,paths2,transport2⟩:=
  split_extension_long_child_normal_world middle lastState live extensions branches size
   frontier branch segment segmentLength matched oldSuffix child world1 kinds1 paths1
   (transport1 segment segmentLength segmentPath) shortSegment inside oldSuffixEq member childValid
   (by rw [firstLocals];exact atBranch) (by rw [firstLocals];exact atSegment)
   (by rw [firstLocals];exact atMatched) (by rw [firstLocals];exact atSuffix)
   (by rw [firstLocals];exact atChild) middleDomain middleCode (by omega) secondRun
 have secondLocals : lastState.locals=middle.locals := by
  apply HolFiniteMapExact.ext;funext name
  have kept:=evaluate_avoidsLocal_flowing name splitExtensionLongChild
   (by simp [splitExtensionLongChild,branchNibbleStore,avoidsLocal]) middle
  rw [secondRun] at kept;exact kept (Or.inl rfl)
 have lastLocals : lastState.locals=s.locals:=secondLocals.trans firstLocals
 have secondMetadata:=evaluateHOLFiniteState_metadata middle splitExtensionLongChild
 rw [secondRun] at secondMetadata
 have lastCode : lastState.code=originalRuntimeCode:=secondMetadata.1.trans middleCode
 have lastDomain : ∀address : BitVec 64,address.toNat<33806089496→ lastState.memaddrs address:=by
  intro address small;rw [secondMetadata.2.1];exact middleDomain address small
 have secondCount:=RunBounded.ofProg split_extension_long_child_bounded middleCode (by omega : 3≤middle.clock)
 unfold RunBounded at secondCount;rw [secondRun] at secondCount;dsimp only at secondCount
 obtain ⟨returnedEq,live3,size3,heap3,sub3,world3,kinds3,paths3,transport3⟩:=
  split_extension_incoming_declaration_returned_world lastState post live2 extensions2 branches size2
   heap2 branch key length matched (length-matched) value valueLength world2 kinds2 paths2
   (transport2 key length (transport1 key length keyPath)) shortKey matchedBound rfl member
   (by rw [lastLocals];exact atBranch) (by rw [lastLocals];exact atKey)
   (by rw [lastLocals];exact atMatched) (by rw [lastLocals];exact atLength)
   (by rw [lastLocals];exact atValue) (by rw [lastLocals];exact atValueLength)
   lastDomain lastCode (by omega) returned tailRun
 exact ⟨returnedEq,live3,extensions2,size3,heap3,fun node h=>sub3 (sub2 h),ext2,
  world3,kinds3,paths3,fun nib len path=>transport3 nib len (transport2 nib len (transport1 nib len path))⟩

#print axioms split_extension_children_returned_world
end InitECandidate.Runtime
