import InitECandidate.Runtime.HashDeleteHash32
import InitECandidate.Runtime.HashDeleteNoMove
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_hash_no_move32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys index stride hole capacity : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (aligned : (keys + index * stride).toNat % 8 = 0)
    (domain : ∀ offset ∈ ([0,8,16,24] : List Nat),
      state.memaddrs (keys + index * stride + BitVec.ofNat 64 offset)) :
    ∃ hash : BitVec 64, ∃ ready, ready.clock = state.clock - 1 ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      (¬ hashDeleteMoveRequired hole index (hash &&& (capacity - 1)) →
        evaluateHOLFiniteState state hashDeleteLoopRest = (none,ready)) := by
  obtain ⟨hash,ready,ticks,memory,globals,postCode,addresses,endian,locals,run⟩ :=
    evaluate_hashDelete_hash32 state keys index stride keysLocal indexLocal strideLocal lengthLocal code clock aligned domain
  refine ⟨hash,ready,ticks,memory,globals,postCode,addresses,endian,locals,?_⟩
  intro noMove
  let entered := setVarHOLFinite (ofString "h") (.val (.word hash)) ready
  have other : ∀ name, name ≠ ofString "h" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have decision := evaluate_hashDelete_no_move entered hole index hash capacity
    ((other _ (by decide)).trans holeLocal) ((other _ (by decide)).trans indexLocal)
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((other _ (by decide)).trans capacityLocal) noMove
  rw [run,decision]
  dsimp only
  have restored := restore_setVar_state ready (ofString "h") (.val (.word hash))
  rw [locals] at restored
  exact congrArg (fun post => (none,post)) restored

#print axioms evaluate_hashDelete_hash_no_move32
end InitECandidate.Runtime
