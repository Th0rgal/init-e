import InitECandidate.Runtime.PayloadOffsetsReturned
import InitECandidate.Runtime.PayloadExtraDataHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original offset-reading/checking and extra-data prefix reaches the
transaction-list call with ordered offsets, exact header writes and unchanged
caller globals/domain. This is extracted from an actual returned suffix. -/
theorem payload_split_entry_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (offsets length payload pointer : BitVec 64) (value : ValueHOL 64)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (header16 : state.memaddrs (payload + 16)) (header24 : state.memaddrs (payload + 24))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 4) = (some (.returned value),post)) :
    ∃ (txs withdrawals balance : BitVec 64) (entry output : PanSemStateFiniteExact 64 F),
      540 ≤ txs.toNat ∧ txs.toNat ≤ 572 ∧ txs.toNat ≤ withdrawals.toNat ∧
      withdrawals.toNat ≤ balance.toNat ∧ balance.toNat ≤ length.toNat ∧
      evaluateHOLFiniteState entry (payloadAt 16) = (some (.returned value),output) ∧
      entry.locals = payloadOffsetLocals state.locals 540 txs withdrawals balance ∧
      entry.code = state.code ∧ entry.memaddrs = state.memaddrs ∧ entry.globals = state.globals ∧
      entry.memory (payload + 16) = .word (pointer + 540) ∧
      entry.memory (payload + 24) = .word (txs - 540) ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  obtain ⟨extra,txs,withdrawals,balance,guardState,output,extraValue,lower,txWd,wdBal,balLength,
      tail,locals,installed,domain,globals,postMemory,postGlobals,postDomain⟩ :=
    payload_offsets_returned state post offsets length value atOffsets atLength domain0 domain8 domain16 domain24 code run
  subst extra
  have atPl : guardState.locals.lookup (ofString "pl") = some (.val (.word payload)) := by
    rw [locals,payload_offset_locals_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact atPayload
  have atP : guardState.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    rw [locals,payload_offset_locals_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact atPointer
  have atExtra : guardState.locals.lookup (ofString "o_extra") = some (.val (.word 540)) := by
    rw [locals]
    simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "o_bal" ≠ ofString "o_extra" by decide,
      show ofString "o_wd" ≠ ofString "o_extra" by decide,
      show ofString "o_txs" ≠ ofString "o_extra" by decide]
  have atTxs : guardState.locals.lookup (ofString "o_txs") = some (.val (.word txs)) := by
    rw [locals]
    simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "o_bal" ≠ ofString "o_txs" by decide,
      show ofString "o_wd" ≠ ofString "o_txs" by decide]
  obtain ⟨small,listRun⟩ := payload_extra_data_prefix_returned guardState output payload pointer 540 txs value
    atPl atP atExtra atTxs (by rw [domain]; exact header16) (by rw [domain]; exact header24)
    (installed.trans code) tail
  have unsigned : (540 : BitVec 64) ≤ txs := by change 540 ≤ txs.toNat; exact lower
  have difference := BitVec.toNat_sub_of_le unsigned
  have upper : txs.toNat ≤ 572 := by
    change (txs - (540 : BitVec 64)).toNat ≤ 32 at small
    rw [difference] at small
    change txs.toNat - 540 ≤ 32 at small
    omega
  let entry := payloadExtraDataHeaderPost guardState payload pointer 540 txs
  have readback := payload_extra_data_header_readback guardState payload pointer 540 txs
  exact ⟨txs,withdrawals,balance,entry,output,lower,upper,txWd,wdBal,balLength,listRun,
    locals,installed,domain,globals,readback.1,readback.2,postMemory,postGlobals,postDomain⟩

#print axioms payload_split_entry_returned
end InitECandidate.Runtime
