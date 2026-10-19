import InitECandidate.Runtime.ValidateHeadersFirstTailSource
import InitECandidate.Runtime.RlpSlicesAdvances
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_validate_headers_increment {F : Type} (s : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index))) :
    evaluateHOLFiniteState s validateHeadersIncrement =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index + 1))) s) := by
  simp [validateHeadersIncrement,evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atIndex,wordOpHOL,wordOp,valueIsWord,valueWord,
    lookupKvarHOLFinite,isValidValueHOLFinite,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,setVarHOLFinite]

/-- Every enabled increment is nonwrapping and strictly decreases n-i. -/
theorem validate_headers_index_progress (index count : BitVec 64) (inside : index.toNat < count.toNat) :
    (index + 1).toNat = index.toNat + 1 ∧ (index + 1).toNat ≤ count.toNat ∧
      count.toNat - (index + 1).toNat < count.toNat - index.toNat :=
  rlpSlices_index_progress index count inside

#print axioms evaluate_validate_headers_increment
#print axioms validate_headers_index_progress
end InitECandidate.Runtime
