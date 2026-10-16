import InitECandidate.Runtime.HashProbeRank
import InitECandidate.Runtime.RunFramesFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

/-- Locate the first loop on the source body's leading scope/sequence spine. -/
def sourceLeadingWhile : ProgHOL 64 → Option (ExpHOL 64 × ProgHOL 64)
  | .while condition body => some (condition,body)
  | .dec _ _ _ body => sourceLeadingWhile body
  | .decCall _ _ _ _ body => sourceLeadingWhile body
  | .seq first _ => sourceLeadingWhile first
  | _ => none

def hashProbeStep (name : MlS) : ProgHOL 64 :=
  .assign .local name (.op .and
    [.op .add [.var .local name,.const 1],
      .op .sub [.var .local (ofString "cap"),.const 1]])

def hashProbeOccupied (name : MlS) : ExpHOL 64 :=
  .cmp .notEqual (.loadByte (.op .add [.var .local (ofString "used"),.var .local name])) (.const 0)

/-- The original insertion function's probe loop uses exactly the increment
whose finite cyclic rank was proved, rather than an assumed replacement loop. -/
theorem source_htabInsert_probe_loop :
    sourceLeadingWhile (sourceFunctionBody Guest.guestFn_htab_insert_raw) =
      some (hashProbeOccupied (ofString "i"),hashProbeStep (ofString "i")) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_htab_insert_raw,declToHOLStructural,funDeclToHOLStructural,
    progToHOLStructural,expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,
    List.map_cons,List.map_nil,Option.map_none,sourceLeadingWhile,hashProbeOccupied,hashProbeStep]
  rfl

/-- Actual assignment evaluation implements the bounded word probe and changes
only the selected local, consuming no source clock. -/
theorem evaluate_hashProbeStep {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (index capacity : BitVec 64)
    (indexLocal : state.locals.lookup name = some (.val (.word index)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))) :
    evaluateHOLFiniteState state (hashProbeStep name) =
      (none,setVarHOLFinite name (.val (.word (hashProbeNext index capacity))) state) := by
  classical
  simp [hashProbeStep,hashProbeNext,evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,
    indexLocal,capacityLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isValidValueHOLExact,
    lookupKvarHOLExact,shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite]
  change setVarHOLFinite name (.val (.word ((index + 1) &&& ((capacity - 1) &&& BitVec.allOnes 64)))) state = _
  rw [BitVec.and_allOnes]
  rfl

/-- The probe condition reads the actual occupancy byte without changing state. -/
theorem eval_hashProbeOccupied {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (index used : BitVec 64) (byte : UInt8)
    (indexLocal : state.locals.lookup name = some (.val (.word index)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + index) = some byte) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (hashProbeOccupied name) =
        some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .notEqual (BitVec.ofNat 64 byte.toNat) 0
          then 1 else 0))) := by
  classical
  simp [hashProbeOccupied,evalHOLExact,evalListHOLExact,indexLocal,usedLocal,
    wordOpHOL,wordOp,valueIsWord,valueWord,loaded]

#print axioms eval_hashProbeOccupied
#print axioms source_htabInsert_probe_loop
#print axioms evaluate_hashProbeStep
end InitECandidate.Runtime
