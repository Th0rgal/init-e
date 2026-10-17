import InitECandidate.Runtime.RlpItemTotalDeclaration
import InitECandidate.Runtime.RlpItemTotalDeclarationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpListCountStep : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_list_count with
  | .dec _ _ _ (.dec _ _ _ (.seq (.while _ body) _)) => body
  | _ => .skip

def rlpListCountUpdates : ProgHOL 64 :=
  match rlpListCountStep with | .decCall _ _ _ _ body => body | _ => .skip

theorem source_rlpListCount_step : rlpListCountStep =
    .decCall (ofString "total") .one (ofString "rlp_item_total")
      [.op .add [.var .local (ofString "p"),.var .local (ofString "off")],
       .op .sub [.var .local (ofString "len"),.var .local (ofString "off")]] rlpListCountUpdates := by
  simp only [rlpListCountStep,rlpListCountUpdates,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_rlpListCount_updates : rlpListCountUpdates =
    .seq (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"),.var .local (ofString "total")]))
      (.assign .local (ofString "count") (.op .add [.var .local (ofString "count"),.const 1])) := by
  simp only [rlpListCountUpdates,rlpListCountStep,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The real list-count assignments advance the offset and count with no
source clock cost; the item-total temporary remains in scope until restoration. -/
theorem evaluate_rlpListCount_updates {F : Type} (state : PanSemStateFiniteExact 64 F)
    (offset count total : BitVec 64)
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (totalLocal : state.locals.lookup (ofString "total") = some (.val (.word total))) :
    evaluateHOLFiniteState state rlpListCountUpdates =
      (none,setVarHOLFinite (ofString "count") (.val (.word (count + 1)))
        (setVarHOLFinite (ofString "off") (.val (.word (offset + total))) state)) := by
  let first := setVarHOLFinite (ofString "off") (.val (.word (offset + total))) state
  have one : evaluateHOLFiniteState state (.assign .local (ofString "off")
      (.op .add [.var .local (ofString "off"),.var .local (ofString "total")])) = (none,first) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,offsetLocal,totalLocal,
      lookupKvarHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,wordOpHOL,wordOp,valueIsWord,valueWord,first]
  have two : evaluateHOLFiniteState first (.assign .local (ofString "count")
      (.op .add [.var .local (ofString "count"),.const 1])) =
      (none,setVarHOLFinite (ofString "count") (.val (.word (count + 1))) first) := by
    have atCount : first.locals.lookup (ofString "count") = some (.val (.word count)) := by
      simpa [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "off" ≠ ofString "count" by decide] using countLocal
    simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atCount,
      lookupKvarHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpListCount_updates,evaluateHOLFiniteState_seq_line780,one]
  exact two

/-- Positive bounded item consumption keeps both assignments non-wrapping,
retains count ≤ offset ≤ length, and strictly decreases remaining input. -/
theorem rlpListCount_update_progress (offset count total length : BitVec 64)
    (countBound : count.toNat ≤ offset.toNat) (offsetBound : offset.toNat ≤ length.toNat)
    (positive : 0 < total.toNat) (bounded : total.toNat ≤ (length - offset).toNat) :
    (offset + total).toNat = offset.toNat + total.toNat ∧
      (count + 1).toNat = count.toNat + 1 ∧
      (count + 1).toNat ≤ (offset + total).toNat ∧ (offset + total).toNat ≤ length.toNat ∧
      length.toNat - (offset + total).toNat < length.toNat - offset.toNat := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr offsetBound)] at bounded
  have limit := length.isLt
  have offsetNoWrap : offset.toNat + total.toNat < 2^64 := by omega
  have countNoWrap : count.toNat + (1 : BitVec 64).toNat < 2^64 := by
    change count.toNat + 1 < 2^64
    omega
  rw [BitVec.toNat_add_of_lt offsetNoWrap,BitVec.toNat_add_of_lt countNoWrap]
  change offset.toNat + total.toNat = offset.toNat + total.toNat ∧
    count.toNat + 1 = count.toNat + 1 ∧ count.toNat + 1 ≤ offset.toNat + total.toNat ∧
    offset.toNat + total.toNat ≤ length.toNat ∧
    length.toNat - (offset.toNat + total.toNat) < length.toNat - offset.toNat
  exact ⟨rfl,rfl,by omega,by omega,by omega⟩

#print axioms evaluate_rlpListCount_updates
#print axioms rlpListCount_update_progress
end InitECandidate.Runtime
