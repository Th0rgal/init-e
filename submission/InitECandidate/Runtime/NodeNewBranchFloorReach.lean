import InitECandidate.Runtime.TrieFreshAllocationFloor
import InitECandidate.Runtime.NodeNewBranchRegistryReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual branch declaration either aborts within its source bound or
provides its concrete constructor witness and the preserved allocation floor. -/
theorem node_new_branch_allocation_floor_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (tail : ProgHOL 64) (pointer : BitVec 64)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64→Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (floor : Nat) (lower : TrieAllocationFloor s live branches floor) (heapAbove : floor≤pointer.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 41≤s.clock) :
 Reaches s (.decCall name .one (ofString "node_new_branch") [] tail)
  (fun next=>NodeNewBranchDeclarationReady s next name pointer live extensions branches ∧
   TrieAllocationFloor next (insert pointer live) (insert pointer branches) floor) 41 tail := by
 have base:=node_new_branch_registry_declaration_reaches s name tail pointer live extensions branches
  world.heap world.capped world.aligned fullDomain world.registry world.owned_below code budget
 apply reaches_mono s _ tail _ _ 41 41 (by omega) _ base
 intro next ready
 exact ⟨ready,ready.allocation_floor world paths lower heapAbove⟩

#print axioms node_new_branch_allocation_floor_reaches
end InitECandidate.Runtime
