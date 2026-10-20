import InitECandidate.Runtime.SplitExtensionSuffixDeclarationFloorWorld
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original split's actual branch allocation followed by its complete
child/payload/return tail. The live returned pointer is the actual allocation
frontier, with concrete allocation failure handled by the original reach proof. -/
theorem split_extension_branch_prefix_returned_floor_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier segment segmentLength key length matched child value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (segmentPath : TriePathBuffer s live size segment segmentLength frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (shortSegment : segmentLength.toNat≤18) (shortKey : length.toNat≤18)
 (inside : matched.toNat<segmentLength.toNat) (matchedBound : matched.toNat≤length.toNat)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤frontier.toNat) (segmentAbove : floor≤segment.toNat) (keyAbove : floor≤key.toNat)
 (childValid : child=0∨child∈live)
 (atSegment : s.locals.lookup (ofString "seg")=some (.val (.word segment)))
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atSegmentLength : s.locals.lookup (ofString "sl")=some (.val (.word segmentLength)))
 (atChild : s.locals.lookup (ofString "child")=some (.val (.word child)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "rl")=some (.val (.word length)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 50≤s.clock)
 (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (splitExtensionAt 3)=(some (.returned returned),post)) :
 returned=.val (.word frontier) ∧
 ∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 insert frontier live⊆larger ∧extensions⊆newExtensions ∧AllocatedTrieWorld post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds post larger newExtensions (insert frontier branches) ∧TrieNodePaths post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieAllocationFloor post larger (insert frontier branches) floor ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 have reached:=allocated_trie_branch_paths_reaches s (ofString "br") (splitExtensionAt 4)
  frontier live extensions branches size world kinds paths fullDomain code (by omega)
 rw [← source_split_extension_3] at reached
 obtain ⟨ready,⟨branchReady,readyWorld,readyKinds,readyPaths⟩,spent,_,agreement,tailReturned⟩:=
  reaches_returned_continuation s _ _ _ 41 returned reached (by rw [run])
 let output:=(evaluateHOLFiniteState ready (splitExtensionAt 4)).2
 have tail : evaluateHOLFiniteState ready (splitExtensionAt 4)=(some (.returned returned),output):=Prod.ext tailReturned rfl
 have readyDomain : ∀address : BitVec 64,address.toNat<33806089496→ ready.memaddrs address:=by
  intro address small;rw [branchReady.domain];exact fullDomain address small
 have readyCode : ready.code=originalRuntimeCode:=branchReady.code.trans code
 have readyChild : child=0∨child∈insert frontier live:=childValid.imp_right (fun h=>Or.inr h)
 obtain ⟨returnedEq,larger,newExtensions,newSize,finish,sub,extSub,worldOut,kindsOut,pathsOut,lowerOut,transport⟩:=
  split_extension_suffix_declaration_returned_floor_world ready output (insert frontier live) extensions (insert frontier branches)
   (Function.update size frontier 176) (allocationEnd frontier 176) frontier segment segmentLength key length matched child value valueLength
   readyWorld readyKinds readyPaths (branchReady.path_buffer world segmentPath) (branchReady.path_buffer world keyPath)
   shortSegment shortKey inside matchedBound floor (branchReady.allocation_floor world paths lower heapAbove)
   (by have bound:=branchReady.extent;omega) segmentAbove keyAbove (Or.inl rfl) readyChild branchReady.atPointer
   ((branchReady.locals _ (by decide)).trans atSegment) ((branchReady.locals _ (by decide)).trans atMatched)
   ((branchReady.locals _ (by decide)).trans atSegmentLength) ((branchReady.locals _ (by decide)).trans atChild)
   ((branchReady.locals _ (by decide)).trans atKey) ((branchReady.locals _ (by decide)).trans atLength)
   ((branchReady.locals _ (by decide)).trans atValue) ((branchReady.locals _ (by decide)).trans atValueLength)
   readyDomain readyCode (by omega) returned tail
 rw [run,tail] at agreement
 have metadata:=evaluateHOLFiniteState_metadata s (splitExtensionAt 3)
 rw [run] at metadata
 have tailMetadata:=evaluateHOLFiniteState_metadata ready (splitExtensionAt 4)
 rw [tail] at tailMetadata
 have memory : post.memory=output.memory:=agreement.2.2.1
 have globals : post.globals=output.globals:=agreement.2.2.2.1
 have domain : post.memaddrs=output.memaddrs:=metadata.2.1.trans (branchReady.domain.symm.trans tailMetadata.2.1.symm)
 have endian : post.be=output.be:=metadata.2.2.1.trans (branchReady.endian.symm.trans tailMetadata.2.2.1.symm)
 refine ⟨returnedEq,larger,newExtensions,newSize,finish,sub,extSub,worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domain endian,lowerOut.after_memory memory,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node member;rw [memory])
 · intro nib len path
   exact (transport nib len (branchReady.path_buffer world path)).after_context memory domain endian

#print axioms split_extension_branch_prefix_returned_floor_world
end InitECandidate.Runtime
