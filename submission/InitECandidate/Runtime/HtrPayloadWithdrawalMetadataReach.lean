import InitECandidate.Runtime.HtrPayloadWithdrawalAllocationSource
import InitECandidate.Runtime.StatelessReach
import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_htrPayload_withdrawal_array : htrPayloadAt 24 =
    .dec (ofString "wd") .one (.load .one (.op .add [.var .local (ofString "pl"),.const 48])) (htrPayloadAt 25) := by rfl

theorem source_htrPayload_withdrawal_count : htrPayloadAt 25 =
    .dec (ofString "nwd") .one (.load .one (.op .add [.var .local (ofString "pl"),.const 56])) (htrPayloadAt 26) := by rfl

theorem htrPayload_withdrawal_metadata_reaches {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload array count : BitVec 64)
    (payloadLocal : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (entry : RlpSliceEntry state payload (3#64) array count) :
    Reaches state (htrPayloadAt 24)
      (fun next => next = setVarHOLFinite (ofString "nwd") (.val (.word count))
        (setVarHOLFinite (ofString "wd") (.val (.word array)) state)) 0 (htrPayloadAt 26) := by
  classical
  have pointerDomain : state.memaddrs (payload + (48#64)) := entry.pointerDomain
  have pointerCell : state.memory (payload + (48#64)) = .word array := entry.pointerCell
  have lengthDomain : state.memaddrs (payload + (56#64)) := by
    simpa only [BitVec.add_assoc,show (3#64) * (16#64) + (8#64) = (56#64) by decide] using entry.lengthDomain
  have lengthCell : state.memory (payload + (56#64)) = .word count := by
    simpa only [BitVec.add_assoc,show (3#64) * (16#64) + (8#64) = (56#64) by decide] using entry.lengthCell
  have countRead : memLoadHOLExact ShapeHOL.one (payload + (56#64)) state.memaddrs state.memory state.structs =
      some (.val (.word count)) := by
    simp [memLoadHOLExact,lengthDomain,lengthCell]
  have first : Reaches state (htrPayloadAt 24)
      (fun next => next = setVarHOLFinite (ofString "wd") (.val (.word array)) state) 0 (htrPayloadAt 25) := by
    rw [source_htrPayload_withdrawal_array]
    apply reaches_dec
    intro value evaluated
    have actual : value = .val (.word array) := by
      simpa [evalHOLExact,evalListHOLExact,payloadLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
        memLoadHOLExact,pointerDomain,pointerCell] using evaluated.symm
    subst value
    exact ⟨array,rfl,rfl⟩
  exact reaches_trans state (htrPayloadAt 24) (htrPayloadAt 25) (htrPayloadAt 26) _ _ 0 0 first (by
    intro next equal
    subst next
    rw [source_htrPayload_withdrawal_count]
    apply reaches_dec
    intro value evaluated
    have actual : value = .val (.word count) := by
      have reduced := evaluated.symm
      simp (config := {decide := true}) [evalHOLExact,evalListHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        payloadLocal,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL] at reduced
      change some value = memLoadHOLExact ShapeHOL.one (payload + (56#64)) state.memaddrs state.memory state.structs at reduced
      rw [countRead] at reduced
      exact Option.some.inj reduced
    subst value
    exact ⟨count,rfl,rfl⟩)

#print axioms source_htrPayload_withdrawal_array
#print axioms source_htrPayload_withdrawal_count
#print axioms htrPayload_withdrawal_metadata_reaches
end InitECandidate.Runtime
