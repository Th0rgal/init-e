import InitECandidate.Runtime.HashDeleteHash32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashDeleteMoveDecision : ProgHOL 64 :=
  match hashDeleteAfterHash with
  | .dec _ _ _ (.dec _ _ _ (.seq decision _)) => decision
  | _ => .skip

def hashDeleteMoveRequired (hole scan home : BitVec 64) : Prop :=
  if hole.toNat ≤ scan.toNat then home.toNat ≤ hole.toNat ∨ scan.toNat < home.toNat
  else home.toNat ≤ hole.toNat ∧ scan.toNat < home.toNat

noncomputable instance (hole scan home : BitVec 64) : Decidable (hashDeleteMoveRequired hole scan home) :=
  Classical.propDecidable _

/-- The real deletion move decision changes only its Boolean local and spends
no source clock, for both the ordinary and wrapped cluster cases. -/
theorem evaluate_hashDelete_move_decision {F : Type} (state : PanSemStateFiniteExact 64 F)
    (hole scan home : BitVec 64)
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (homeLocal : state.locals.lookup (ofString "home") = some (.val (.word home)))
    (movableLocal : state.locals.lookup (ofString "movable") = some (.val (.word (0 : BitVec 64)))) :
    evaluateHOLFiniteState state hashDeleteMoveDecision =
      (none,if hashDeleteMoveRequired hole scan home then
        setVarHOLFinite (ofString "movable") (.val (.word (1 : BitVec 64))) state else state) := by
  classical
  unfold hashDeleteMoveDecision hashDeleteAfterHash hashDeleteLoopRest
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,Option.orElse,hashDeleteLeadingWhile]
  by_cases hs : hole.toNat ≤ scan.toNat <;> by_cases hh : home.toNat ≤ hole.toNat <;> by_cases sh : scan.toNat < home.toNat <;>
    simp [evaluateHOLFiniteState_ite,evaluateHOLFiniteState_assign,evaluateHOLFiniteState_skip,
      evalHOLExact,evalListHOLExact,holeLocal,scanLocal,homeLocal,movableLocal,
      Compiler.Encoders.Asm.wordCmpHOL,wordOpHOL,wordOp,valueIsWord,valueWord,
      hashDeleteMoveRequired,hs,hh,sh,BitVec.lt_def,BitVec.le_def,Nat.not_lt,lookupKvarHOLExact,
      isValidValueHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,OrOp.or,AndOp.and]

#print axioms evaluate_hashDelete_move_decision
end InitECandidate.Runtime
