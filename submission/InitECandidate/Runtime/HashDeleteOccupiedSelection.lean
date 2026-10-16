import InitECandidate.Runtime.HashDeleteEmptyExit
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Nonempty occupancy selects the actual hash/move continuation after
advancing j; it does not execute the empty-slot break. -/
theorem evaluate_hashDelete_occupied_iteration {F : Type}
    (state : PanSemStateFiniteExact 64 F) (index capacity used : BitVec 64) (byte : UInt8)
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (loadedBefore : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (used + hashProbeNext index capacity) = some byte)
    (occupied : byte ≠ 0) :
    evaluateHOLFiniteState state hashDeleteLoopBody =
      evaluateHOLFiniteState
        (setVarHOLFinite (ofString "j") (.val (.word (hashProbeNext index capacity))) state) hashDeleteLoopRest := by
  classical
  let advanced := setVarHOLFinite (ofString "j") (.val (.word (hashProbeNext index capacity))) state
  have j : advanced.locals.lookup (ofString "j") = some (.val (.word (hashProbeNext index capacity))) := by
    simp [advanced,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have distinct : ofString "j" ≠ ofString "used" := by decide
  have u : advanced.locals.lookup (ofString "used") = some (.val (.word used)) := by
    simpa [advanced,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct] using usedLocal
  have loaded : @panMemLoadByteHOL 64 _ advanced.memory advanced.memaddrs
      (fun address => Classical.propDecidable (advanced.memaddrs address)) advanced.be
      (used + hashProbeNext index capacity) = some byte := loadedBefore
  have condition : @evalHOLExact 64 F _ advanced.toExact
      (fun address => Classical.propDecidable (advanced.memaddrs address)) hashDeleteEmpty =
      some (.val (.word (0 : BitVec 64))) := by
    simp [hashDeleteEmpty,evalHOLExact,evalListHOLExact,j,u,wordOpHOL,wordOp,valueIsWord,valueWord,
      loaded,Compiler.Encoders.Asm.wordCmpHOL]
    have nonzero : byte.toNat ≠ 0 := by
      intro zero
      apply occupied
      exact UInt8.toNat_inj.mp zero
    have small := byte.toNat_lt
    intro equal
    have natural := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat,BitVec.toNat_zero] at natural
    rw [Nat.mod_eq_of_lt (show byte.toNat < 2 ^ 64 by omega)] at natural
    exact nonzero natural
  unfold hashDeleteLoopBody
  rw [evaluateHOLFiniteState_seq_line780,evaluate_hashProbeStep state _ index capacity indexLocal capacityLocal]
  change evaluateHOLFiniteState advanced (.seq (.ite hashDeleteEmpty .break .skip) hashDeleteLoopRest) = _
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
  simp [evaluateHOLFiniteState_skip,advanced]

#print axioms evaluate_hashDelete_occupied_iteration
end InitECandidate.Runtime
