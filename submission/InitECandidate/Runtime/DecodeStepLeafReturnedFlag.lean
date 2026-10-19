import InitECandidate.Runtime.DecodeStepPathDispatchBound
import InitECandidate.Runtime.PanDecCallReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_leaf_stores_returned_flag {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepLeafStores = (some (.returned value),post)) :
    ∃ leaf : ValueHOL 64, value = .rStruct [.val (.word (0 : BitVec 64)),leaf] := by
  rw [source_decodeStep_leaf_stores] at run
  obtain ⟨first,_,tailRun⟩ := seq_returned_of_nonreturning_first
    (by intro v; exact evaluate_noDirectReturn _ rfl s v) run
  obtain ⟨second,_,returned⟩ := seq_returned_of_nonreturning_first
    (by intro v; exact evaluate_noDirectReturn _ rfl first v) tailRun
  cases atLeaf : second.locals.lookup (ofString "lf") with
  | none => simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atLeaf] at returned
  | some leaf =>
    have result : (if sizeOfShapeWithContextHOL second.structs
        (shapeOfHOLExact (.rStruct [.val (.word (0 : BitVec 64)),leaf])) ≤ 32
        then some (PanSemResultExact.returned (.rStruct [.val (.word (0 : BitVec 64)),leaf]))
        else some .error) = some (.returned value) := by
      simpa [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atLeaf,apply_ite] using congrArg Prod.fst returned
    split at result
    · exact ⟨leaf,(PanSemResultExact.returned.inj (Option.some.inj result)).symm⟩
    · cases result

/-- The original constructor's actual tail returns the completed-node tag. -/
theorem decode_step_leaf_construction_returned_flag {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepLeafConstruction = (some (.returned value),post)) :
    ∃ leaf : ValueHOL 64, value = .rStruct [.val (.word (0 : BitVec 64)),leaf] := by
  rw [source_decodeStep_leaf_construction] at run
  obtain ⟨allocated,ready,output,_,_,tailRun,_⟩ := evaluate_decCall_returned_continuation s post
    (ofString "lf") (ofString "node_new_leaf") .one _ decodeStepLeafStores value run
  exact decode_step_leaf_stores_returned_flag _ output value tailRun

/-- Parsing the leaf value cannot return a stack-push tag, regardless of the
callee's memory effects or the shape of malformed caller locals. -/
theorem decode_step_leaf_branch_returned_flag {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepLeafBranch = (some (.returned value),post)) :
    ∃ leaf : ValueHOL 64, value = .rStruct [.val (.word (0 : BitVec 64)),leaf] := by
  rw [source_decode_step_leaf_branch] at run
  obtain ⟨parsed,ready,output,_,_,tailRun,_⟩ := evaluate_decCall_returned_continuation s post
    (ofString "vi") (ofString "rlp_item") (.comb [.one,.one,.one,.one]) _ decodeStepLeafValueContinuation value run
  rw [source_decodeStep_leaf_value_continuation] at tailRun
  obtain ⟨next,_,constructionRun⟩ := seq_returned_of_nonreturning_first
    (by intro v; exact evaluate_noDirectReturn _ rfl _ v) tailRun
  exact decode_step_leaf_construction_returned_flag next output value constructionRun

#print axioms decode_step_leaf_stores_returned_flag
#print axioms decode_step_leaf_construction_returned_flag
#print axioms decode_step_leaf_branch_returned_flag
end InitECandidate.Runtime
