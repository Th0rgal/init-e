import InitECandidate.Runtime.HashFindArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Concrete table locals and allocated-array domains discharge all argument,
alignment and readability premises of an actual32-byte lookup iteration. -/
theorem evaluate_hashFind_ready32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride key index capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (strideFits : 32 ≤ stride.toNat)
    (inside : index.toNat < capacity.toNat)
    (bounded : keys.toNat + capacity.toNat * stride.toNat ≤ 33806089496)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))) :
    ∃ result post, evaluateHOLFiniteState state hashFindIteration = (result,post) ∧
      (result = none ∨ result = some (.returned (.val (.word index)))) ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (result = none → post.locals.lookup (ofString "i") = some (.val (.word (hashProbeNext index capacity)))) ∧
      (result = none → post.locals = (setVarHOLFinite (ofString "i")
        (.val (.word (hashProbeNext index capacity))) state).locals) := by
  have arguments := eval_hashFind_arguments state keys index stride key 32 keysLocal indexLocal strideLocal keyLocal lengthLocal
  have slot := hashFind_slot_address keys index stride capacity inside bounded keysAligned strideAligned
  have domain : ∀ offset ∈ ([0,8,16,24] : List Nat),
      state.memaddrs (keys + index * stride + BitVec.ofNat 64 offset) ∧ state.memaddrs (key + BitVec.ofNat 64 offset) := by
    intro offset member
    have small : offset < 32 := by simp at member; omega
    have interval := hashFind_slot_offset keys index stride capacity 32 offset inside bounded keysAligned strideAligned
      (by change 32 ≤ stride.toNat; exact strideFits) (by change offset < 32; exact small)
    exact ⟨arrayDomain _ interval.2.1 interval.2.2,keyDomain offset member⟩
  exact evaluate_hashFind_iteration32 state (keys + index * stride) key index capacity
    arguments code clock slot.2 keyAligned domain indexLocal capLocal

#print axioms evaluate_hashFind_ready32
end InitECandidate.Runtime
