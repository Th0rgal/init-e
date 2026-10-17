import InitECandidate.Runtime.HashFindTableReady20
import InitECandidate.Runtime.HashFindOccupied32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashFind_table_occupied20 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key index : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant 20 table keys stride capacity used values order orderPos count bits state)
    (clock : 2 ≤ state.clock) (inside : index.toNat < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < 20 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < 20 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (20 : BitVec 64))))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (byte : UInt8)
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (used + index) = some byte)
    (occupied : BitVec.ofNat 64 byte.toNat ≠ 0) :
    ∃ result post, evaluateHOLFiniteState state hashFindLoop =
        (match result with | none => evaluateHOLFiniteState post hashFindLoop | some _ => (result,post)) ∧
      (result = none ∨ result = some (.returned (.val (.word index)))) ∧
      post.clock = state.clock - 2 ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (result = none → post.locals.lookup (ofString "i") = some (.val (.word (hashProbeNext index capacity)))) ∧
      (result = none → post.locals = (setVarHOLFinite (ofString "i")
        (.val (.word (hashProbeNext index capacity))) state).locals) := by
  have condition := eval_hashProbeOccupied state (ofString "i") index used byte indexLocal usedLocal loaded
  have flag : Compiler.Encoders.Asm.wordCmpHOL .notEqual (BitVec.ofNat 64 byte.toNat) 0 = true := by
    have nonzero : BitVec.ofNat 64 byte.toNat ≠ (0#64) := occupied
    simp [Compiler.Encoders.Asm.wordCmpHOL,nonzero]
  have entryInvariant := invariant.after_read state (decClockHOLFinite state) 20 table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  obtain ⟨result,post,body,outcome,ticks,memory,globals,postCode,addresses,endian,next,locals⟩ :=
    evaluate_hashFind_table_ready20 (decClockHOLFinite state) table keys stride capacity used values order orderPos count key index bits
      entryInvariant (by change state.clock - 1 ≠ 0; omega) inside keyAligned keyWords keyBytes
      keysLocal strideLocal keyLocal lengthLocal indexLocal capLocal
  have ticks' : post.clock = state.clock - 2 := by
    change post.clock = state.clock - 1 - 1 at ticks
    omega
  refine ⟨result,post,?_,outcome,ticks',memory,globals,postCode,addresses,endian,next,locals⟩
  unfold hashFindLoop
  rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
  rw [if_pos flag]
  simp only [show state.clock ≠ 0 by omega,if_false,body]
  have fixed : fixClockHOLFinite (decClockHOLFinite state) (result,post) = (result,post) := by
    simp [fixClockHOLFinite,decClockHOLFinite,show ¬ state.clock - 1 < post.clock by omega]
  rw [fixed]
  rcases outcome with noneResult | returnedResult
  · rw [noneResult]
    rfl
  · rw [returnedResult]
    rfl
#print axioms evaluate_hashFind_table_occupied20
end InitECandidate.Runtime
