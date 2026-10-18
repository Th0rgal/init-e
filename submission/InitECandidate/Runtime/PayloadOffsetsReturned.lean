import InitECandidate.Runtime.PayloadOffsetCheckEntryLocals
import InitECandidate.Runtime.PayloadOffsetCheckSuffixReturned
import InitECandidate.Runtime.PayloadOffsetBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned original payload offset-reading suffix reaches its extra-data
guard with concrete ordered offsets and the exact four added local bindings. -/
theorem payload_offsets_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (offsets length : BitVec 64) (value : ValueHOL 64)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 4) = (some (.returned value),post)) :
    ∃ (extra txs withdrawals balance : BitVec 64) (entry output : PanSemStateFiniteExact 64 F),
      extra = 540 ∧ 540 ≤ txs.toNat ∧ txs.toNat ≤ withdrawals.toNat ∧
      withdrawals.toNat ≤ balance.toNat ∧ balance.toNat ≤ length.toNat ∧
      evaluateHOLFiniteState entry (payloadAt 13) = (some (.returned value),output) ∧
      entry.locals = payloadOffsetLocals state.locals extra txs withdrawals balance ∧
      entry.code = state.code ∧ entry.memaddrs = state.memaddrs ∧ entry.globals = state.globals ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  obtain ⟨extra,txs,withdrawals,balance,checked,output,tail,clock,domain,globals,installed,locals,
      read0,read8,read16,read24,postMemory,postGlobals,postDomain⟩ :=
    payload_returned_offset_check_entry_locals state post offsets value atOffsets domain0 domain8 domain16 domain24 run
  have atLengthChecked : checked.locals.lookup (ofString "len") = some (.val (.word length)) := by
    rw [locals,payload_offset_locals_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact atLength
  have atOffsetsChecked : checked.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by
    rw [globals]; exact atOffsets
  obtain ⟨_,first,accepted,entry,callRun,continuation,memory,sameGlobals,sameDomain,sameLocals⟩ :=
    payload_offset_check_suffix_returned checked output offsets length value atOffsetsChecked atLengthChecked
      (installed.trans code) tail
  have extraRead : memWord checked.memory offsets = extra := by
    have cell : checked.memory offsets = .word extra := by simpa using read0
    simp [memWord,cell]
  have txRead : memWord checked.memory (offsets + 8) = txs := by unfold memWord; rw [read8]
  have wdRead : memWord checked.memory (offsets + 16) = withdrawals := by unfold memWord; rw [read16]
  have balRead : memWord checked.memory (offsets + 24) = balance := by unfold memWord; rw [read24]
  obtain ⟨extraValue,txLower,txWd,wdBal,balLength⟩ :=
    payload_offset_bounds checked offsets length extra txs withdrawals balance first accepted extraRead txRead wdRead balRead
  have metadata := evaluateHOLFiniteState_metadata checked payloadOffsetCheckCall
  rw [callRun] at metadata
  exact ⟨extra,txs,withdrawals,balance,entry,output,extraValue,txLower,txWd,wdBal,balLength,
    continuation,sameLocals.trans locals,metadata.1.trans installed,sameDomain.trans domain,sameGlobals.trans globals,
    postMemory,postGlobals,postDomain⟩

#print axioms payload_offsets_returned
end InitECandidate.Runtime
