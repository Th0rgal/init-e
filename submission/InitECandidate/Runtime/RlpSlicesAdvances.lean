import InitECandidate.Runtime.RlpSlicesSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpSlicesAdvances : ProgHOL 64 :=
  match rlpSlicesUpdates with
  | .seq _ (.seq _ advances) => advances
  | _ => .skip

theorem source_rlpSlices_advances : rlpSlicesAdvances =
    .seq (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"),.var .local (ofString "total")]))
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) := by
  simp only [rlpSlicesAdvances,rlpSlicesUpdates,rlpSlicesStep,rlpSlicesLoop,rlpSlicesLoopAndReturn,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_rlpSlices_advances {F : Type} (state : PanSemStateFiniteExact 64 F)
    (offset index total : BitVec 64)
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (totalLocal : state.locals.lookup (ofString "total") = some (.val (.word total))) :
    evaluateHOLFiniteState state rlpSlicesAdvances =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index + 1)))
        (setVarHOLFinite (ofString "off") (.val (.word (offset + total))) state)) := by
  let first := setVarHOLFinite (ofString "off") (.val (.word (offset + total))) state
  have one : evaluateHOLFiniteState state (.assign .local (ofString "off")
      (.op .add [.var .local (ofString "off"),.var .local (ofString "total")])) = (none,first) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,offsetLocal,totalLocal,
      lookupKvarHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,wordOpHOL,wordOp,valueIsWord,valueWord,first]
  have two : evaluateHOLFiniteState first (.assign .local (ofString "i")
      (.op .add [.var .local (ofString "i"),.const 1])) =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index + 1))) first) := by
    have atCount : first.locals.lookup (ofString "i") = some (.val (.word index)) := by
      simpa [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "off" ≠ ofString "i" by decide] using indexLocal
    simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atCount,
      lookupKvarHOLExact,isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpSlices_advances,evaluateHOLFiniteState_seq_line780,one]
  exact two

/-- The actual loop guard ensures index increment cannot wrap and
strictly decreases the number of remaining slices, independently of offsets. -/
theorem rlpSlices_index_progress (index count : BitVec 64) (enabled : index.toNat < count.toNat) :
    (index + 1).toNat = index.toNat + 1 ∧ (index + 1).toNat ≤ count.toNat ∧
      count.toNat - (index + 1).toNat < count.toNat - index.toNat := by
  have limit := count.isLt
  rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2^64; omega)]
  change index.toNat + 1 = index.toNat + 1 ∧ index.toNat + 1 ≤ count.toNat ∧
    count.toNat - (index.toNat + 1) < count.toNat - index.toNat
  exact ⟨rfl,by omega,by omega⟩

#print axioms evaluate_rlpSlices_advances
#print axioms rlpSlices_index_progress
end InitECandidate.Runtime
