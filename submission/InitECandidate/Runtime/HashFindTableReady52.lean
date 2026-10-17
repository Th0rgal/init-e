import InitECandidate.Runtime.HashFindIteration52
import InitECandidate.Runtime.HashTableKeySlotDomains
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Table geometry supplies all slot comparison domains for 52-byte keys. -/
theorem evaluate_hashFind_table_ready52 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key index : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant 52 table keys stride capacity used values order orderPos count bits state)
    (clock : state.clock ≠ 0) (inside : index.toNat < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < 52 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < 52 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (52 : BitVec 64))))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))) :
    ∃ result post, evaluateHOLFiniteState state hashFindIteration = (result,post) ∧
      (result = none ∨ result = some (.returned (.val (.word index)))) ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (result = none → post.locals.lookup (ofString "i") = some (.val (.word (hashProbeNext index capacity)))) ∧
      (result = none → post.locals = (setVarHOLFinite (ofString "i")
        (.val (.word (hashProbeNext index capacity))) state).locals) := by
  have slot := invariant.key_slot_domains state 52 table keys stride capacity used values order orderPos count index bits inside
  have arguments := eval_hashFind_arguments state keys index stride key 52 keysLocal indexLocal strideLocal keyLocal lengthLocal
  apply evaluate_hashFind_iteration52 state (keys + index * stride) key index capacity arguments invariant.code clock slot.1 keyAligned
  · intro offset member
    have small : offset < 52 := by simp at member; omega
    exact ⟨(slot.2 offset small).1,keyWords offset small⟩
  · intro offset member
    have small : offset < 52 := by simp at member; omega
    exact ⟨(slot.2 offset small).2,keyBytes offset small⟩
  · exact indexLocal
  · exact capLocal

#print axioms evaluate_hashFind_table_ready52
end InitECandidate.Runtime
