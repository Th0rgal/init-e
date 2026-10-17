import InitECandidate.Runtime.HashDeleteHashSupported
import InitECandidate.Runtime.HashDeleteHashMove32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_hash_move_supported {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys index stride hole capacity keyLength : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (aligned : (keys + index * stride).toNat % 8 = 0)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (words : ∀ offset : Nat, offset < keyLength.toNat →
      state.memaddrs (keys + index * stride + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < keyLength.toNat →
      state.memaddrs (panByteAlignHOL (keys + index * stride + BitVec.ofNat 64 offset))) :
    ∃ hash : BitVec 64, ∃ ready, ready.clock = state.clock - 1 ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      (∀ post : PanSemStateFiniteExact 64 F,
        hashDeleteMoveRequired hole index (hash &&& (capacity - 1)) →
        evaluateHOLFiniteState
          (hashDeleteMoveEntry (setVarHOLFinite (ofString "h") (.val (.word hash)) ready) hash capacity)
          hashDeleteMoveBody = (none,post) →
        evaluateHOLFiniteState state hashDeleteLoopRest =
          (none,hashDeleteHashExit state
            (hashDeleteMoveExit (setVarHOLFinite (ofString "h") (.val (.word hash)) ready) post))) := by
  obtain ⟨hash,ready,ticks,memory,globals,postCode,addresses,endian,locals,run⟩ :=
    evaluate_hashDelete_hash_supported state keys index stride keyLength keysLocal indexLocal strideLocal lengthLocal code clock aligned supported words bytes
  refine ⟨hash,ready,ticks,memory,globals,postCode,addresses,endian,locals,?_⟩
  intro post moves movement
  let entered := setVarHOLFinite (ofString "h") (.val (.word hash)) ready
  have other : ∀ name, name ≠ ofString "h" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have decision := evaluate_hashDelete_move_scope_run entered post hole index hash capacity
    ((other _ (by decide)).trans holeLocal) ((other _ (by decide)).trans indexLocal)
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((other _ (by decide)).trans capacityLocal) moves movement
  rw [run,decision]
  rfl

#print axioms evaluate_hashDelete_hash_move_supported
end InitECandidate.Runtime
