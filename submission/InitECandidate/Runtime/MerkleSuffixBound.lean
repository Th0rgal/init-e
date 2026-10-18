import InitECandidate.Runtime.MerkleLevelsInputBound
import InitECandidate.Runtime.MerklePaddingBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem runBounded_merkleDepth {F : Type} (state : PanSemStateFiniteExact 64 F)
    (dn target : BitVec 64)
    (depth : state.locals.lookup (ofString "dn") = some (.val (.word dn)))
    (limit : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (small : dn.toNat ≤ 27) (targetBound : target.toNat ≤ 63)
    (code : state.code = originalRuntimeCode) (budget : merklePaddingCost + 17 ≤ state.clock) :
    RunBounded state (merkleizeAt 11) (merklePaddingCost + 17) := by
  rw [source_merkleDepth_declaration]
  apply RunBounded.decWord state (ofString "d") _ dn (by simpa [evalHOLExact] using depth)
  apply runBounded_merklePaddingSuffix _ dn target
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "d" ≠ ofString "target" by decide] using limit
  · omega
  · exact targetBound
  · exact code
  · exact budget

def merkleSuffixCost : Nat := merkleInputTreeCost + (merklePaddingCost + 17)

/-- Complete actual Merkle suffix from the level loop through padding, copy,
heap release and return, with the caller's decoded size/depth facts. -/
theorem runBounded_merkleSuffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (cur dn target : BitVec 64)
    (counter : state.locals.lookup (ofString "cur") = some (.val (.word cur)))
    (depth : state.locals.lookup (ofString "dn") = some (.val (.word dn)))
    (limit : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (chunkBound : cur.toNat ≤ 134217728) (depthBound : dn.toNat ≤ 27) (targetBound : target.toNat ≤ 63)
    (code : state.code = originalRuntimeCode) (budget : merkleSuffixCost ≤ state.clock) :
    RunBounded state (merkleizeAt 10) merkleSuffixCost := by
  rw [source_merkleLevels]
  change RunBounded state (.seq (.while merkleLevelsCondition merkleLevelBody) (merkleizeAt 11)) _
  refine RunBounded.seq (runBounded_merkleInputLevels state cur counter chunkBound code
    (by unfold merkleSuffixCost at budget; omega)) budget ?_
  intro next run nextCode remaining
  have depthFrame := evaluate_avoidsLocal_flowing (ofString "dn")
    (.while merkleLevelsCondition merkleLevelBody) (by decide) state (by rw [run]; exact Or.inl rfl)
  have limitFrame := evaluate_avoidsLocal_flowing (ofString "target")
    (.while merkleLevelsCondition merkleLevelBody) (by decide) state (by rw [run]; exact Or.inl rfl)
  rw [run] at depthFrame limitFrame
  exact runBounded_merkleDepth next dn target (depthFrame.trans depth) (limitFrame.trans limit)
    depthBound targetBound (nextCode.trans code) remaining

theorem source_merkleCur_declaration : merkleizeAt 9 =
    .dec (ofString "cur") .one (.var .local (ofString "size")) (merkleizeAt 10) := by rfl

theorem runBounded_merkleCurSuffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (size dn target : BitVec 64)
    (sizeLocal : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (depth : state.locals.lookup (ofString "dn") = some (.val (.word dn)))
    (limit : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (chunkBound : size.toNat ≤ 134217728) (depthBound : dn.toNat ≤ 27) (targetBound : target.toNat ≤ 63)
    (code : state.code = originalRuntimeCode) (budget : merkleSuffixCost ≤ state.clock) :
    RunBounded state (merkleizeAt 9) merkleSuffixCost := by
  rw [source_merkleCur_declaration]
  apply RunBounded.decWord state (ofString "cur") _ size (by simpa [evalHOLExact] using sizeLocal)
  apply runBounded_merkleSuffix _ size dn target
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "cur" ≠ ofString "dn" by decide] using depth
  · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "cur" ≠ ofString "target" by decide] using limit
  · exact chunkBound
  · exact depthBound
  · exact targetBound
  · exact code
  · exact budget

#print axioms runBounded_merkleDepth
#print axioms runBounded_merkleSuffix
#print axioms source_merkleCur_declaration
#print axioms runBounded_merkleCurSuffix
end InitECandidate.Runtime
