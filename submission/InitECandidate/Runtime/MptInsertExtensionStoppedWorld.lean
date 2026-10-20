import InitECandidate.Runtime.MptInsertExtensionDispatchSplitWorld
import InitECandidate.Runtime.MptInsertExtensionAdvanceGo
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A stopped normal extension dispatch must be the actual split path:
full matches set go=1. Both source loads and all constructors are included. -/
theorem mpt_insert_extension_dispatch_stopped_world {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (frontier node key length level value valueLength oldResult : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (keyPath : TriePathBuffer s live size key length frontier) (short : length.toNat≤18)
 (extension : node∈extensions)
 (levelBound : level.toNat≤length.toNat)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (atKey : s.locals.lookup (ofString "key")=some (.val (.word key)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atValue : s.locals.lookup (ofString "vptr")=some (.val (.word value)))
 (atValueLength : s.locals.lookup (ofString "vlen")=some (.val (.word valueLength)))
 (atResult : s.locals.lookup (ofString "r")=some (.val (.word oldResult)))
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 71≤s.clock)
 (stopped : post.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertExtensionDispatch=(none,post)) :
 ∃root : BitVec 64,∃larger newExtensions : Set (BitVec 64),∃newSize : BitVec 64→Nat,∃finish : BitVec 64,
 post.locals.lookup (ofString "r")=some (.val (.word root)) ∧root∈larger ∧live⊆larger ∧extensions⊆newExtensions ∧
 AllocatedTrieWorld post larger newExtensions (insert frontier branches) newSize finish ∧
 TrieNodeKinds post larger newExtensions (insert frontier branches) ∧
 TrieNodePaths post larger newExtensions (insert frontier branches) newSize finish ∧
 (∀nib len,TriePathBuffer s live size nib len frontier→TriePathBuffer post larger newSize nib len finish) ∧
 (∀other : MlS,other≠ofString "r"→ other≠ofString "br"→post.locals.lookup other=s.locals.lookup other) := by
 have alternatives:=mpt_insert_extension_dispatch_split_world s post live extensions branches size
  frontier node key length level value valueLength oldResult world kinds paths keyPath short extension
  levelBound atNode atKey atLength atLevel atValue atValueLength atResult fullDomain code budget run
 rcases alternatives with matched | splitWorld
 · obtain ⟨found,ready,output,_,_,_,advance,_,_,go⟩:=matched
   have one:=mpt_insert_extension_advance_normal_go ready output advance
   rw [one] at go
   rw [stopped] at go
   exact False.elim (by cases go)
 · exact splitWorld

#print axioms mpt_insert_extension_dispatch_stopped_world
end InitECandidate.Runtime
