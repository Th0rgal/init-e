import InitECandidate.Runtime.HashDeleteLoopSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual deletion iteration breaks immediately on the first scanned empty
byte, before hashing, copying, or moving any order entry. -/
theorem evaluate_hashDelete_empty_iteration {F : Type}
    (state : PanSemStateFiniteExact 64 F) (index capacity used : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (empty : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (used + hashProbeNext index capacity) = some 0) :
    evaluateHOLFiniteState state hashDeleteLoopBody =
      (some .break,setVarHOLFinite (ofString "j") (.val (.word (hashProbeNext index capacity))) state) := by
  classical
  let advanced := setVarHOLFinite (ofString "j") (.val (.word (hashProbeNext index capacity))) state
  have j : advanced.locals.lookup (ofString "j") = some (.val (.word (hashProbeNext index capacity))) := by
    simp [advanced,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have distinct : ofString "j" ≠ ofString "used" := by decide
  have u : advanced.locals.lookup (ofString "used") = some (.val (.word used)) := by
    simpa [advanced,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct] using usedLocal
  have loaded : @panMemLoadByteHOL 64 _ advanced.memory advanced.memaddrs
      (fun address => Classical.propDecidable (advanced.memaddrs address)) advanced.be
      (used + hashProbeNext index capacity) = some 0 := empty
  have condition : @evalHOLExact 64 F _ advanced.toExact
      (fun address => Classical.propDecidable (advanced.memaddrs address)) hashDeleteEmpty =
      some (.val (.word (1 : BitVec 64))) := by
    simp [hashDeleteEmpty,evalHOLExact,evalListHOLExact,j,u,wordOpHOL,wordOp,valueIsWord,valueWord,
      loaded,Compiler.Encoders.Asm.wordCmpHOL]
  unfold hashDeleteLoopBody
  rw [evaluateHOLFiniteState_seq_line780,evaluate_hashProbeStep state _ index capacity indexLocal capacityLocal]
  change evaluateHOLFiniteState advanced (.seq (.ite hashDeleteEmpty .break .skip) hashDeleteLoopRest) = _
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
  simp [evaluateHOLFiniteState_break,advanced]

#print axioms evaluate_hashDelete_empty_iteration
end InitECandidate.Runtime
