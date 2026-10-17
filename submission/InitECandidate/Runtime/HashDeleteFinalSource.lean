import InitECandidate.Runtime.SourceByteReadback
import InitECandidate.Runtime.HashDeleteLoopRanked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

/-- Original deletion statements after the bounded scan. -/
def hashDeleteFinalTail : ProgHOL 64 :=
  match sourceFindLocalScope (ofString "j") (sourceFunctionBody Guest.guestFn_htab_del) with
  | some (.dec _ _ _ (.seq _ tail)) => tail
  | _ => .skip

def hashDeleteClear : ProgHOL 64 :=
  .storeByte (.op .add [.var .local (ofString "used"),.var .local (ofString "i")]) (.const 0)

def hashDeleteCountTail : ProgHOL 64 :=
  match hashDeleteFinalTail with
  | .seq _ tail => tail
  | _ => .skip

theorem source_hashDelete_scan_scope :
    sourceFindLocalScope (ofString "j") (sourceFunctionBody Guest.guestFn_htab_del) =
      some (.dec (ofString "j") .one (.var .local (ofString "i")) (.seq hashDeleteLoop hashDeleteFinalTail)) := by
  unfold hashDeleteFinalTail hashDeleteLoop hashDeleteLoopBody hashDeleteLoopRest
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none,Option.orElse,hashDeleteLeadingWhile,
    sourceFindLocalScope,hashDeleteEmpty,hashProbeStep]
  rfl

theorem source_hashDelete_final_tail : hashDeleteFinalTail = .seq hashDeleteClear hashDeleteCountTail := by
  unfold hashDeleteCountTail hashDeleteFinalTail hashDeleteClear
  simp only [sourceFunctionBody,declToHOL_eq,Guest.guestFn_htab_del,declToHOLStructural,
    funDeclToHOLStructural,progToHOLStructural,expToHOLStructural,expListToHOLStructural,
    shapeToHOLStructural,List.map_cons,List.map_nil,sourceFindLocalScope]
  rfl

theorem evaluate_hashDelete_clear {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used hole cell : BitVec 64)
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (domain : state.memaddrs (panByteAlignHOL (used + hole)))
    (memory : state.memory (panByteAlignHOL (used + hole)) = .word cell) :
    evaluateHOLFiniteState state hashDeleteClear = (none,sourceWriteByte state (used + hole) 0 cell) ∧
      hashOccupancyRead (sourceWriteByte state (used + hole) 0 cell) used hole = some 0 := by
  constructor
  · unfold hashDeleteClear
    apply evaluate_source_storeByte
    · simp [evalHOLExact,evalListHOLExact,usedLocal,holeLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    · rfl
    · exact domain
    · exact memory
  · exact sourceWriteByte_load_self state (used + hole) 0 cell domain

#print axioms evaluate_hashDelete_clear

#print axioms source_hashDelete_scan_scope
#print axioms source_hashDelete_final_tail
end InitECandidate.Runtime
