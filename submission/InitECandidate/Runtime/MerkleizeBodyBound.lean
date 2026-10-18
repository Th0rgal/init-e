import InitECandidate.Runtime.MerkleTargetBound
import InitECandidate.Runtime.CeilLog2GeneralDeclaration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def merkleCountDepthCost : Nat := 65 + merkleTargetCost
def merkleBodyCost : Nat := 65 + merkleCountDepthCost

theorem source_merkleCountDepth : merkleizeAt 1 =
    .decCall (ofString "dn") .one (ofString "ceil_log2") [.var .local (ofString "n")] (merkleizeAt 2) := by rfl

theorem source_merkleLimitDepth : merkleizeAt 0 =
    .decCall (ofString "dl") .one (ofString "ceil_log2") [.var .local (ofString "limit")] (merkleizeAt 1) := by rfl

theorem runBounded_merkleCountDepth {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer n dl heap : BitVec 64)
    (input : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (limitDepth : state.locals.lookup (ofString "dl") = some (.val (.word dl)))
    (small : n.toNat ≤ 134217712) (limitBound : dl.toNat ≤ 63)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : merkleCountDepthCost ≤ state.clock) :
    RunBounded state (merkleizeAt 1) merkleCountDepthCost := by
  rw [source_merkleCountDepth]
  refine runBounded_ceilLog2_decCall_inputBound state (ofString "dn") _ _ n merkleTargetCost code
    (by simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,count]) small budget ?_
  intro dn post bounded lengths postCode _ _ _ globals remaining
  let next := setVarHOLFinite (ofString "dn") (.val (.word dn)) {post with locals := state.locals}
  have keep (key : MlS) (different : key ≠ ofString "dn") :
      next.locals.lookup key = state.locals.lookup key := by
    simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  exact runBounded_merkleTarget next pointer n dl dn heap ((keep _ (by decide)).trans input)
    ((keep _ (by decide)).trans count) ((keep _ (by decide)).trans limitDepth)
    (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) lengths limitBound bounded
    (by change post.globals.lookup _ = _; rw [globals]; exact heapLocal)
    heapBound (postCode.trans code) remaining

/-- Complete original merkleize runtime bound from word arguments, checked
input size and a capped real heap. Every outcome is covered; successful
allocation, readable input arrays and readable output are not assumed. -/
theorem runBounded_merkleize_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer n limit heap : BitVec 64)
    (input : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (limitLocal : state.locals.lookup (ofString "limit") = some (.val (.word limit)))
    (small : n.toNat ≤ 134217712)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : merkleBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_merkleize) merkleBodyCost := by
  rw [sourceFunctionBody_eq_structural]
  change RunBounded state (merkleizeAt 0) merkleBodyCost
  rw [source_merkleLimitDepth]
  refine runBounded_ceilLog2_decCall state (ofString "dl") _ _ limit merkleCountDepthCost code
    (by simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,limitLocal]) budget ?_
  intro dl post bounded _ postCode _ _ _ globals remaining
  let next := setVarHOLFinite (ofString "dl") (.val (.word dl)) {post with locals := state.locals}
  have keep (key : MlS) (different : key ≠ ofString "dl") :
      next.locals.lookup key = state.locals.lookup key := by
    simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  exact runBounded_merkleCountDepth next pointer n dl heap ((keep _ (by decide)).trans input)
    ((keep _ (by decide)).trans count)
    (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) small bounded
    (by change post.globals.lookup _ = _; rw [globals]; exact heapLocal)
    heapBound (postCode.trans code) remaining

theorem merkleBodyCost_value : merkleBodyCost = 2467972597275435636 := by decide

#print axioms source_merkleCountDepth
#print axioms source_merkleLimitDepth
#print axioms runBounded_merkleCountDepth
#print axioms runBounded_merkleize_body
#print axioms merkleBodyCost_value
end InitECandidate.Runtime
