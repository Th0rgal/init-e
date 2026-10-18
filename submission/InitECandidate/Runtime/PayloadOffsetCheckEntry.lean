import InitECandidate.Runtime.TransactionDataScopedBound
import InitECandidate.Runtime.PayloadOffsetReadWords
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned offset-reading prefix reaches the original offset checker with
its four concrete table cells installed. -/
theorem payload_returned_offset_check_entry {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (offsets : BitVec 64) (value : ValueHOL 64)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (run : evaluateHOLFiniteState state (payloadAt 4) = (some (.returned value),post)) :
    ∃ (extra txs withdrawals balance : BitVec 64) (entry output : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState entry (payloadAt 12) = (some (.returned value),output) ∧
      entry.clock = state.clock ∧ entry.memaddrs = state.memaddrs ∧ entry.globals = state.globals ∧
      entry.memory (offsets + 0) = .word extra ∧ entry.memory (offsets + 8) = .word txs ∧
      entry.memory (offsets + 16) = .word withdrawals ∧ entry.memory (offsets + 24) = .word balance ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  obtain ⟨extra,txs,withdrawals,balance,output,tail,memory,globals,domain⟩ :=
    payload_offset_reads_returned_words state post value run
  let ready := setVarHOLFinite (ofString "o_bal") (.val (.word balance))
    (setVarHOLFinite (ofString "o_wd") (.val (.word withdrawals))
      (setVarHOLFinite (ofString "o_txs") (.val (.word txs))
        (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state)))
  have stored := evaluate_payload_offset_stores ready offsets extra txs withdrawals balance atOffsets
    (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "o_txs" ≠ ofString "o_extra" by decide,show ofString "o_wd" ≠ ofString "o_extra" by decide,show ofString "o_wd" ≠ ofString "o_txs" by decide,show ofString "o_bal" ≠ ofString "o_extra" by decide,show ofString "o_bal" ≠ ofString "o_txs" by decide,show ofString "o_bal" ≠ ofString "o_wd" by decide])
    (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "o_txs" ≠ ofString "o_extra" by decide,show ofString "o_wd" ≠ ofString "o_extra" by decide,show ofString "o_wd" ≠ ofString "o_txs" by decide,show ofString "o_bal" ≠ ofString "o_extra" by decide,show ofString "o_bal" ≠ ofString "o_txs" by decide,show ofString "o_bal" ≠ ofString "o_wd" by decide])
    (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "o_txs" ≠ ofString "o_extra" by decide,show ofString "o_wd" ≠ ofString "o_extra" by decide,show ofString "o_wd" ≠ ofString "o_txs" by decide,show ofString "o_bal" ≠ ofString "o_extra" by decide,show ofString "o_bal" ≠ ofString "o_txs" by decide,show ofString "o_bal" ≠ ofString "o_wd" by decide])
    (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "o_txs" ≠ ofString "o_extra" by decide,show ofString "o_wd" ≠ ofString "o_extra" by decide,show ofString "o_wd" ≠ ofString "o_txs" by decide,show ofString "o_bal" ≠ ofString "o_extra" by decide,show ofString "o_bal" ≠ ofString "o_txs" by decide,show ofString "o_bal" ≠ ofString "o_wd" by decide])
    domain0 domain8 domain16 domain24
  have grouping : evaluateHOLFiniteState ready (.seq payloadOffsetStores (payloadAt 12)) =
      evaluateHOLFiniteState ready (payloadAt 8) := by
    rw [source_payload_offset_stores]
    unfold payloadOffsetStores
    rw [evaluate_seq_assoc]
    apply evaluate_seq_second_congr
    intro middle
    rw [evaluate_seq_assoc]
    apply evaluate_seq_second_congr
    intro next
    exact evaluate_seq_assoc next _ _ _
  change evaluateHOLFiniteState ready (payloadAt 8) = _ at tail
  rw [← grouping,evaluateHOLFiniteState_seq_line780,stored] at tail
  have cells := payload_offset_stores_readback ready offsets extra txs withdrawals balance
  exact ⟨extra,txs,withdrawals,balance,journalRecordPost32 ready offsets extra txs withdrawals balance,output,
    tail,rfl,rfl,rfl,cells.1,cells.2.1,cells.2.2.1,cells.2.2.2,memory,globals,domain⟩

#print axioms payload_returned_offset_check_entry
end InitECandidate.Runtime
