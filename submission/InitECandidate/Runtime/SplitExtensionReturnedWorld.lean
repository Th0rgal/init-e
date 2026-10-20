import InitECandidate.Runtime.SplitExtensionBranchPrefixWorld
import InitECandidate.Runtime.SplitExtensionLoadsReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original _split_extension returned-world endpoint. The allocated
extension record earns all three real read domains; stored headers earn the
old segment path and live child. Every callee and both actual split sides are
included, without a future-callee/frame/runtime/heap-room premise. -/
theorem split_extension_returned_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node segment segmentLength key length matched child value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier)
 (shortKey : length.toNat≤18)
 (inside : matched.toNat<segmentLength.toNat) (matchedBound : matched.toNat≤length.toNat)
 (extension : node∈extensions)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (memory32 : s.memory (node+32#64)=.word segment)
 (memory40 : s.memory (node+40#64)=.word segmentLength)
 (memory48 : s.memory (node+48#64)=.word child)
 (atMatched : s.locals.lookup (ofString "pl")=some (.val (.word matched)))
 (atKey : s.locals.lookup (ofString "rk")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "rl")=some (.val (.word length)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 50≤s.clock)
 (returned : ValueHOL 64)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__split_extension)=(some (.returned returned),post)) :
 returned=.val (.word frontier) ∧
 ∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 insert frontier live⊆larger ∧extensions⊆newExtensions ∧AllocatedTrieWorld post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds post larger newExtensions (insert frontier branches) ∧TrieNodePaths post larger newExtensions (insert frontier branches) newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) := by
 have liveNode : node∈live:=world.layout.extensionLive extension
 have nonBranch : node∉branches:=fun branch=>Set.disjoint_left.mp world.layout.differentKinds extension branch
 obtain ⟨storedKey,storedLength,keyAt,lengthAt,shortSegment,storedPath⟩:=paths.paths node liveNode nonBranch
 have storedKeyAt : s.memory (node+32#64)=.word storedKey:=keyAt
 have storedLengthAt : s.memory (node+40#64)=.word storedLength:=lengthAt
 have keyEq : storedKey=segment:=HolWordLab.word.inj (storedKeyAt.symm.trans memory32)
 have lengthEq : storedLength=segmentLength:=HolWordLab.word.inj (storedLengthAt.symm.trans memory40)
 rw [keyEq,lengthEq] at storedPath
 rw [lengthEq] at shortSegment
 have childValid : child=0∨child∈live:=world.registry.extensionChildren node extension child memory48
 have domain (offset : Nat) (small : offset<56) : s.memaddrs (node+BitVec.ofNat 64 offset) := by
  apply fullDomain
  have capacity:=world.layout.extensionSize node extension
  rw [world.layout.field_nat node liveNode offset (by omega)]
  have allocated:=world.allocated node liveNode
  have capped:=world.capped
  omega
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (splitExtensionAt 0)=(some (.returned returned),post) at run
 obtain ⟨output,tailRun,memory,globals,domains,endian⟩:=split_extension_loads_returned_scope s post node segment segmentLength child
  atNode (domain 32 (by decide)) (domain 40 (by decide)) (domain 48 (by decide)) memory32 memory40 memory48 returned run
 let ready:=splitExtensionLoadedState s segment segmentLength child
 have readyWorld : AllocatedTrieWorld ready live extensions branches size frontier:=world.after_memory_globals rfl rfl
 have readyKinds : TrieNodeKinds ready live extensions branches:=
  kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive (by intro node member;rfl)
 have readyLocal (name : MlS) (seg : name≠ofString "seg") (sl : name≠ofString "sl") (childName : name≠ofString "child") :
  ready.locals.lookup name=s.locals.lookup name := by
  simp [ready,splitExtensionLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
   seg,Ne.symm seg,sl,Ne.symm sl,childName,Ne.symm childName]
 obtain ⟨returnedEq,larger,newExtensions,newSize,finish,sub,extSub,worldOut,kindsOut,pathsOut,transport⟩:=
  split_extension_branch_prefix_returned_world ready output live extensions branches size
   frontier segment segmentLength key length matched child value valueLength
   readyWorld readyKinds (paths.after_context rfl rfl rfl)
   (storedPath.after_context rfl rfl rfl) (keyPath.after_context rfl rfl rfl)
   shortSegment shortKey inside matchedBound childValid
   (by simp (config:={decide:=true}) [ready,splitExtensionLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   ((readyLocal _ (by decide) (by decide) (by decide)).trans atMatched)
   (by simp (config:={decide:=true}) [ready,splitExtensionLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp [ready,splitExtensionLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
   ((readyLocal _ (by decide) (by decide) (by decide)).trans atKey)
   ((readyLocal _ (by decide) (by decide) (by decide)).trans atLength)
   ((readyLocal _ (by decide) (by decide) (by decide)).trans atValue)
   ((readyLocal _ (by decide) (by decide) (by decide)).trans atValueLength)
   fullDomain code budget returned tailRun
 refine ⟨returnedEq,larger,newExtensions,newSize,finish,sub,extSub,worldOut.after_memory_globals memory globals,?_,pathsOut.after_context memory domains endian,?_⟩
 · exact kindsOut.after_kind_frame worldOut.layout.extensionLive worldOut.layout.branchLive (by intro node member;rw [memory])
 · intro nib len path
   exact (transport nib len (path.after_context rfl rfl rfl)).after_context memory domains endian

#print axioms split_extension_returned_world
end InitECandidate.Runtime
