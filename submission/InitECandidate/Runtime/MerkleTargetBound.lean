import InitECandidate.Runtime.MerkleEmptyBound
import InitECandidate.Runtime.MaximumReturned
import InitECandidate.Runtime.VmFn_max
import InitECandidate.Runtime.PanTwoWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def merkleTargetCost : Nat := 1 + merkleAfterTargetCost

theorem source_merkleTarget : merkleizeAt 2 =
    .decCall (ofString "target") .one (ofString "max")
      [.var .local (ofString "dl"),.var .local (ofString "dn")] (merkleizeAt 3) := by rfl

/-- The original max call supplies the actual padding-depth bound and keeps
the heap/global frame used by the following allocation. -/
theorem runBounded_merkleTarget {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer n dl dn heap : BitVec 64)
    (input : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (limitDepth : state.locals.lookup (ofString "dl") = some (.val (.word dl)))
    (depth : state.locals.lookup (ofString "dn") = some (.val (.word dn)))
    (lengths : MerkleChunkLengths n ((1#64) <<< dn.toNat))
    (limitBound : dl.toNat ≤ 63) (depthBound : dn.toNat ≤ 27)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : merkleTargetCost ≤ state.clock) :
    RunBounded state (merkleizeAt 2) merkleTargetCost := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "dl"),.var .local (ofString "dn")] = some [.val (.word dl),.val (.word dn)] := by
    simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,limitDepth,depth]
  rw [source_merkleTarget]
  refine RunBounded.decCall args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "max") =
      some ([(ofString "a",.one),(ofString "b",.one)],sourceFunctionBody Guest.guestFn_max,.one) := by
    rw [code]
    exact vmLookup_max
  rw [pan_two_word_lookup state.code.lookup (ofString "max") (ofString "a") (ofString "b")
    (sourceFunctionBody Guest.guestFn_max) dl dn (by decide) installed] at lookup
  cases lookup
  constructor
  · exact RunBounded.ofProg (ProgBounded.straight _ (by rw [sourceFunctionBody_eq_structural]; rfl))
      code (Nat.zero_le _)
  · intro value post run remaining
    let entry := callEntryStateHOLFinite state
      ((HolFiniteMapExact.empty.update (ofString "a",.val (.word dl))).update (ofString "b",.val (.word dn)))
    have left : entry.locals.lookup (ofString "a") = some (.val (.word dl)) := by
      simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "b" ≠ ofString "a" by decide]
    have right : entry.locals.lookup (ofString "b") = some (.val (.word dn)) := by
      simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    obtain ⟨target,valueEq,bounded,postEq⟩ := max_body_returned_bound entry post dl dn value 63 left right
      limitBound (by omega) run
    rw [valueEq]
    let next := setVarHOLFinite (ofString "target") (.val (.word target)) {post with locals := state.locals}
    have keep (key : MlS) (different : key ≠ ofString "target") :
        next.locals.lookup key = state.locals.lookup key := by
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    have globals : next.globals = state.globals := by
      change post.globals = state.globals
      rw [postEq]
      rfl
    have nextCode : next.code = state.code := by
      change post.code = state.code
      rw [postEq]
      rfl
    exact runBounded_merkleAfterTarget next pointer n dn target heap
      ((keep _ (by decide)).trans input) ((keep _ (by decide)).trans count)
      ((keep _ (by decide)).trans depth)
      (by simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) lengths depthBound bounded
      (by rw [globals]; exact heapLocal) heapBound (nextCode.trans code) remaining

#print axioms source_merkleTarget
#print axioms runBounded_merkleTarget
end InitECandidate.Runtime
