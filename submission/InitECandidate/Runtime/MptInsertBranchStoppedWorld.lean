import InitECandidate.Runtime.MptInsertBranchStoppedSource
import InitECandidate.Runtime.MptInsertBranchValueNormalPaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete stopped branch dispatch retains the world and every separated
path, with the payload arm earned from the actual branch condition and go. -/
theorem mpt_insert_branch_dispatch_stopped_paths_world {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
    (frontier : BitVec 64)
    (world : AllocatedTrieWorld state live extensions branches size frontier)
    (kinds : TrieNodeKinds state live extensions branches)
    (paths : TrieNodePaths state live extensions branches size frontier)
    (node value length oldResult level keyLength : BitVec 64) (registered : node ∈ branches)
    (nodeLocal : state.locals.lookup (ofString "node") = some (.val (.word node)))
    (valueLocal : state.locals.lookup (ofString "vptr") = some (.val (.word value)))
    (lengthLocal : state.locals.lookup (ofString "vlen") = some (.val (.word length)))
    (resultLocal : state.locals.lookup (ofString "r") = some (.val (.word oldResult)))
    (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→state.memaddrs address)
    (atLevel : state.locals.lookup (ofString "level")=some (.val (.word level)))
    (atKeyLength : state.locals.lookup (ofString "klen")=some (.val (.word keyLength)))
    (stopped : post.locals.lookup (ofString "go")=some (.val (.word (0#64))))
    (run : evaluateHOLFiniteState state mptInsertBranchDispatch=(none,post)) :
    AllocatedTrieWorld post live extensions branches size frontier ∧
    TrieNodeKinds post live extensions branches ∧TrieNodePaths post live extensions branches size frontier ∧
    post.locals.lookup (ofString "r")=some (.val (.word node)) ∧
    (∀key keyLength,TriePathBuffer state live size key keyLength frontier→
      TriePathBuffer post live size key keyLength frontier) := by
 obtain ⟨_,payload⟩:=mpt_insert_branch_dispatch_stopped state post level keyLength atLevel atKeyLength stopped run
 exact mpt_insert_branch_value_normal_paths_world state post live extensions branches size frontier
  world kinds paths node value length oldResult registered nodeLocal valueLocal lengthLocal resultLocal fullDomain payload

#print axioms mpt_insert_branch_dispatch_stopped_paths_world
end InitECandidate.Runtime
