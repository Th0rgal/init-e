import InitECandidate.Runtime.HashProbeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashFindDecision : ProgHOL 64 :=
  .seq (.ite (.cmp .notEqual (.var .local (ofString "eq")) (.const 0))
      (.return (.var .local (ofString "i"))) .skip)
    (hashProbeStep (ofString "i"))

def hashFindComparisonAddress : ExpHOL 64 :=
  .op .add [.var .local (ofString "keys"),
    .panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]]

/-- The actual lookup loop compares keys and either returns its current
index or executes the same bounded probe increment used by insertion. -/
theorem source_htabFind_probe_loop :
    sourceLeadingWhile (sourceFunctionBody Guest.guestFn_htab_find_slot) =
      some (hashProbeOccupied (ofString "i"),
        .decCall (ofString "eq") .one (ofString "memeq")
          [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")]
          hashFindDecision) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  simp only [Guest.guestFn_htab_find_slot,declToHOLStructural,funDeclToHOLStructural,
    progToHOLStructural,expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,
    List.map_cons,List.map_nil,sourceLeadingWhile,hashProbeOccupied,
    hashProbeStep,hashFindDecision,hashFindComparisonAddress]
  rfl

/-- A failed key comparison advances the actual lookup probe at zero clocks. -/
theorem evaluate_hashFind_mismatch {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index capacity : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (equalLocal : state.locals.lookup (ofString "eq") = some (.val (.word (0 : BitVec 64)))) :
    evaluateHOLFiniteState state hashFindDecision =
      (none,setVarHOLFinite (ofString "i") (.val (.word (hashProbeNext index capacity))) state) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.var .local (ofString "eq")) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
    simp [evalHOLExact,equalLocal,Compiler.Encoders.Asm.wordCmpHOL]
  unfold hashFindDecision
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  rw [condition]
  simp only [evaluateHOLFiniteState_skip]
  exact evaluate_hashProbeStep state (ofString "i") index capacity indexLocal capacityLocal

/-- A successful comparison exits lookup immediately with the current index. -/
theorem evaluate_hashFind_match {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index equal : BitVec 64) (nonzero : equal ≠ 0)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (equalLocal : state.locals.lookup (ofString "eq") = some (.val (.word equal))) :
    evaluateHOLFiniteState state hashFindDecision =
      (some (.returned (.val (.word index))),emptyLocalsHOLFinite state) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.var .local (ofString "eq")) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
    simp [evalHOLExact,equalLocal,Compiler.Encoders.Asm.wordCmpHOL]
    exact nonzero
  unfold hashFindDecision
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
  simp [evaluateHOLFiniteState_return,evalHOLExact,indexLocal,shapeOfHOLExact]

#print axioms evaluate_hashFind_match
#print axioms source_htabFind_probe_loop
#print axioms evaluate_hashFind_mismatch
end InitECandidate.Runtime
