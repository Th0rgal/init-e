import InitECandidate.Runtime.TrieLeafAllocationFloor
import InitECandidate.Runtime.NodeNewLeafAssignmentReady
import InitECandidate.Runtime.FreshTrieNodePaths
import InitECandidate.Runtime.FreshTrieNodeKinds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual leaf assignment call earns the fresh record and preserves the
full old world and every separated path, without an allocation-room oracle. -/
theorem node_new_leaf_assignment_allocation_floor {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (pointer nib length value valueLength : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (keyPath : TriePathBuffer s live size nib length pointer) (short : length.toNat≤18)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤pointer.toNat) (keyAbove : floor≤nib.toNat)
 (name : MlS) (arguments : List (ExpHOL 64))
 (args : evalListHOLFinite s (h:=fun address=>Classical.propDecidable (s.memaddrs address)) arguments=
  some [.val (.word nib),.val (.word length),.val (.word value),.val (.word valueLength)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (.call (some (some (.local,name),none)) (ofString "node_new_leaf") arguments)=(none,post)) :
 TrieAllocationFloor post (insert pointer live) branches floor := by
 have ready:=node_new_leaf_assignment_ready s post name arguments pointer nib length value valueLength
  live extensions branches args world.heap world.capped fullDomain world.registry world.owned_below code run
 exact ready.allocation_floor world paths lower heapAbove keyAbove

#print axioms node_new_leaf_assignment_allocation_floor
end InitECandidate.Runtime
