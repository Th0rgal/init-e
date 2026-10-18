import InitECandidate.Runtime.PayloadSplitHeaderFrame
import InitECandidate.Runtime.PayloadOffsetCheckEntryLocals
import InitECandidate.Runtime.PayloadOffsetCheckSuffixReturned
import InitECandidate.Runtime.PayloadExtraDataHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The returned payload suffix from the offset reads on keeps every watched
word outside the scratch offset table, payload+16..128 and the fresh heap,
and every global other than heap_ptr. -/
theorem payload_offset_header_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (offsets length payload pointer heapPointer w : BitVec 64) (value : ValueHOL 64)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (header16 : state.memaddrs (payload + 16)) (header24 : state.memaddrs (payload + 24))
    (header32 : state.memaddrs (payload + 32)) (header40 : state.memaddrs (payload + 40))
    (sepOffsets : w ≠ offsets ∧ w ≠ offsets + 8 ∧ w ≠ offsets + 16 ∧ w ≠ offsets + 24)
    (sepHeader : w ≠ payload + 16 ∧ w ≠ payload + 24)
    (separate : ∀ offset : BitVec 64, offset ∈ ([32,40,48,56,64,72,80,88,96,104,112,120,128] : List (BitVec 64)) →
      w ≠ payload + offset)
    (below : w.toNat < heapPointer.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 4) = (some (.returned value),post)) :
    post.memory w = state.memory w ∧ GlobalsExceptHeap state post := by
  obtain ⟨extra,txs,withdrawals,balance,output,tail,memory,globals,domain⟩ :=
    payload_offset_reads_returned_words state post value run
  generalize hready : setVarHOLFinite (ofString "o_bal") (.val (.word balance))
    (setVarHOLFinite (ofString "o_wd") (.val (.word withdrawals))
      (setVarHOLFinite (ofString "o_txs") (.val (.word txs))
        (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state))) = ready at tail
  have rl : ready.locals = payloadOffsetLocals state.locals extra txs withdrawals balance := by rw [← hready]; rfl
  have rother : ∀ k, k ≠ ofString "o_extra" → k ≠ ofString "o_txs" → k ≠ ofString "o_wd" → k ≠ ofString "o_bal" →
      ready.locals.lookup k = state.locals.lookup k := by
    intro k a b c d; rw [rl]; exact payload_offset_locals_other _ _ _ _ _ k a b c d
  have rtx : ready.locals.lookup (ofString "o_txs") = some (.val (.word txs)) := by
    rw [rl]; simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "o_bal" ≠ ofString "o_txs" by decide,show ofString "o_wd" ≠ ofString "o_txs" by decide]
  have rwd : ready.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)) := by
    rw [rl]; simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "o_bal" ≠ ofString "o_wd" by decide]
  have rbal : ready.locals.lookup (ofString "o_bal") = some (.val (.word balance)) := by
    rw [rl]; simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE]
  have rext : ready.locals.lookup (ofString "o_extra") = some (.val (.word extra)) := by
    rw [rl]; simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "o_bal" ≠ ofString "o_extra" by decide,show ofString "o_wd" ≠ ofString "o_extra" by decide,
      show ofString "o_txs" ≠ ofString "o_extra" by decide]
  have rg : ready.globals = state.globals := by rw [← hready]; rfl
  have rm : ready.memory = state.memory := by rw [← hready]; rfl
  have rd : ready.memaddrs = state.memaddrs := by rw [← hready]; rfl
  have rc : ready.code = state.code := by rw [← hready]; rfl
  have stored := evaluate_payload_offset_stores ready offsets extra txs withdrawals balance (by rw [rg]; exact atOffsets)
    rext rtx rwd rbal (by rw [rd]; exact domain0) (by rw [rd]; exact domain8) (by rw [rd]; exact domain16)
    (by rw [rd]; exact domain24)
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
  rw [← grouping, evaluateHOLFiniteState_seq_line780, stored] at tail
  dsimp only at tail
  generalize hJ : journalRecordPost32 ready offsets extra txs withdrawals balance = J at tail
  have Jl : J.locals = ready.locals := by rw [← hJ]; rfl
  have Jg : J.globals = ready.globals := by rw [← hJ]; rfl
  have Jd : J.memaddrs = ready.memaddrs := by rw [← hJ]; rfl
  have Jc : J.code = ready.code := by rw [← hJ]; rfl
  have Jw : J.memory w = ready.memory w := by
    rw [← hJ]
    simp only [journalRecordPost32, sourceWriteWord]
    rw [if_neg sepOffsets.2.2.2, if_neg sepOffsets.2.2.1, if_neg sepOffsets.2.1, if_neg sepOffsets.1]
  obtain ⟨_, _, _, entry3, callRun, cont, m3, g3, d3, l3⟩ := payload_offset_check_suffix_returned J output offsets length value
    (by rw [Jg, rg]; exact atOffsets)
    (by rw [Jl]; exact (rother _ (by decide) (by decide) (by decide) (by decide)).trans atLength)
    (by rw [Jc, rc]; exact code) tail
  have el : ∀ k, entry3.locals.lookup k = ready.locals.lookup k := by intro k; rw [l3, Jl]
  have meta3 := evaluateHOLFiniteState_metadata J payloadOffsetCheckCall
  rw [callRun] at meta3
  have c3 : entry3.code = originalRuntimeCode := meta3.1.trans (Jc.trans (rc.trans code))
  obtain ⟨_, listRun⟩ := payload_extra_data_prefix_returned entry3 output payload pointer extra txs value
    ((el _).trans ((rother _ (by decide) (by decide) (by decide) (by decide)).trans atPayload))
    ((el _).trans ((rother _ (by decide) (by decide) (by decide) (by decide)).trans atPointer))
    ((el _).trans rext) ((el _).trans rtx) (by rw [d3, Jd, rd]; exact header16) (by rw [d3, Jd, rd]; exact header24)
    c3 cont
  generalize hH : payloadExtraDataHeaderPost entry3 payload pointer extra txs = H at listRun
  have hl : ∀ k, H.locals.lookup k = ready.locals.lookup k := by intro k; rw [← hH, ← el k]; rfl
  have Hg : H.globals = state.globals := by rw [← hH]; show entry3.globals = _; rw [g3, Jg, rg]
  have Hd : H.memaddrs = state.memaddrs := by rw [← hH]; show entry3.memaddrs = _; rw [d3, Jd, rd]
  have Hc : H.code = originalRuntimeCode := by rw [← hH]; exact c3
  have Hw : H.memory w = entry3.memory w := by
    rw [← hH]
    simp only [payloadExtraDataHeaderPost, sourceWriteWord]
    rw [if_neg sepHeader.2, if_neg sepHeader.1]
  obtain ⟨fm, fg⟩ := payload_split_header_frame H output payload pointer txs withdrawals balance heapPointer w value
    ((hl _).trans ((rother _ (by decide) (by decide) (by decide) (by decide)).trans atPayload))
    ((hl _).trans ((rother _ (by decide) (by decide) (by decide) (by decide)).trans atPointer))
    ((hl _).trans rtx) ((hl _).trans rwd) ((hl _).trans rbal) (by rw [Hg]; exact heap) heapBound
    (by rw [Hd]; exact header32) (by rw [Hd]; exact header40) separate below Hc listRun
  refine ⟨?_, ?_⟩
  · rw [memory, fm, Hw, m3, Jw, rm]
  · intro k hk
    rw [globals, fg k hk, Hg]

#print axioms payload_offset_header_frame
end InitECandidate.Runtime
