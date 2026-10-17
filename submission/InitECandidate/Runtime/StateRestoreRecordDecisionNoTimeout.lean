import InitECandidate.Runtime.StateRestoreRecordSource
import InitECandidate.Runtime.HashTableReadySetAllPlansCeilingNoTimeout
import InitECandidate.Runtime.HashTableReadyDeleteSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual rollback decision is bounded whether it restores or deletes a key. -/
theorem HashTableReady.restore_record_decision_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key record present value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (capacityLarge : 1 < capacity.toNat)
    (ticks : 2 ^ 72 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (presentDomain : state.memaddrs (record + 16)) (presentCell : state.memory (record + 16) = .word present)
    (valueDomain : state.memaddrs (record + 24)) (valueCell : state.memory (record + 24) = .word value)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (evaluateHOLFiniteState state stateRestoreRecordDecision).1 ≠ some .timeOut ∧
    state.clock ≤ (evaluateHOLFiniteState state stateRestoreRecordDecision).2.clock + 2 ^ 72 ∧
      (evaluateHOLFiniteState state stateRestoreRecordDecision).2.clock ≤ state.clock := by
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have u := ready.live.arrays.usedBefore
    have o := ready.live.arrays.orderBefore
    have e := ready.live.arrays.endBound
    omega
  have loadPresent : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress (ofString "r") 16)) = some (.val (.word present)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress state (ofString "r") record 16 r]
    simp [memLoadHOLExact]
    exact ⟨presentDomain,presentCell⟩
  have loadValue : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress (ofString "r") 24)) = some (.val (.word value)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress state (ofString "r") record 24 r]
    simp [memLoadHOLExact]
    exact ⟨valueDomain,valueCell⟩
  classical
  by_cases zero : present = 0
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      rw [evalHOLExact,loadPresent]
      simp [evalHOLExact,zero,Compiler.Encoders.Asm.wordCmpHOL]
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k]
    obtain ⟨post,run,_,cost,remaining,_⟩ := ready.delete_call_supported state keyLength table pointer keys stride capacity used values order orderPos items key bits supported
      _ _ args keyAligned keyWords keyBytes (by omega)
    unfold stateRestoreRecordDecision
    rw [evaluateHOLFiniteState_ite,condition]
    dsimp only
    rw [run]
    simpa using (show (none : Option (PanSemResultExact 64)) ≠ some .timeOut ∧ state.clock ≤ post.clock + 2 ^ 72 ∧ post.clock ≤ state.clock from ⟨by simp,by omega,remaining⟩)
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0)) = some (.val (.word (1 : BitVec 64))) := by
      rw [evalHOLExact,loadPresent]
      simp only [evalHOLExact,Compiler.Encoders.Asm.wordCmpHOL]
      simpa using zero
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)] =
        some [.val (.word table),.val (.word key),.val (.word value)] := by
      simp only [evalListHOLFinite,evalListHOLExact]
      rw [loadValue]
      simp [evalHOLExact,t,k]
    have bounded := ready.set_call_supported_all_plans_ceiling_no_timeout state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
      strideBound ready.live.frontier.aligned ready.live.frontier.bounded capacityBound ticks ready.live.frontier.heap domain
      _ _ _ args capacityLarge keyAligned keyWords keyBytes
    unfold stateRestoreRecordDecision
    rw [evaluateHOLFiniteState_ite,condition]
    exact bounded

#print axioms HashTableReady.restore_record_decision_no_timeout
end InitECandidate.Runtime
