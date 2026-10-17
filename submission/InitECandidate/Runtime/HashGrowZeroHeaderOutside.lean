import InitECandidate.Runtime.HashGrowZeroHeader
import InitECandidate.Runtime.HashGrowHeaderOccupancy
import InitECandidate.Runtime.HashGrowHeaderState
import InitECandidate.Runtime.HashGrowHeaderOutside
import InitECandidate.Runtime.MemzeroAlignedCombinedCall
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Execute the original zeroing call and seven header stores before entering
rehash, retaining the old key width and stride and an empty occupancy count. -/
theorem evaluate_htabGrow_zero_header_outside {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity keys values used order orderPos : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 1 ≤ state.clock)
    (aligned : used.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ used.toNat)
    (bounded : used.toNat + capacity.toNat ≤ 33806089496)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (ncapLocal : state.locals.lookup (ofString "ncap") = some (.val (.word capacity)))
    (nkeysLocal : state.locals.lookup (ofString "nkeys") = some (.val (.word keys)))
    (nvalsLocal : state.locals.lookup (ofString "nvals") = some (.val (.word values)))
    (nusedLocal : state.locals.lookup (ofString "nused") = some (.val (.word used)))
    (norderLocal : state.locals.lookup (ofString "norder") = some (.val (.word order)))
    (norder_posLocal : state.locals.lookup (ofString "norder_pos") = some (.val (.word orderPos)))
    (headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (used + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (panByteAlignHOL (used + BitVec.ofNat 64 offset))) :
    ∃ ready, evaluateHOLFiniteState state (hashGrowZeroHeader continuation) = evaluateHOLFiniteState ready continuation ∧
      hashOccupiedCount capacity (hashOccupancyRead ready used) = 0 ∧
      state.clock ≤ ready.clock + capacity.toNat + 1 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ready.memory (table + 0) = state.memory (table + 0) ∧ ready.memory (table + 8) = state.memory (table + 8) ∧
      ready.memory (table + 16) = .word capacity ∧ ready.memory (table + 24) = .word 0 ∧
      ready.memory (table + 32) = .word keys ∧ ready.memory (table + 40) = .word values ∧
      ready.memory (table + 48) = .word used ∧ ready.memory (table + 56) = .word order ∧ ready.memory (table + 64) = .word orderPos ∧
      (∀ watched : BitVec 64, (watched.toNat < table.toNat ∨ table.toNat + 72 ≤ watched.toNat) → watched.toNat < used.toNat →
        ready.memory watched = state.memory watched) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "nused"),.var .local (ofString "ncap")] = some [.val (.word used),.val (.word capacity)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,nusedLocal,ncapLocal]
  obtain ⟨zeroed,zeroRun,_,cost,remaining,globals,postCode,addresses,endian,locals,empty,frame⟩ :=
    evaluate_memzero_aligned_call_with_frame state _ _ used capacity arguments code ticks bounded aligned wordDomain byteDomain
  have protectedHeaders : ∀ offset : Nat, offset ≤ 64 →
      zeroed.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have before : (table + BitVec.ofNat 64 offset).toNat < used.toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
      omega
    have separate := memcpy_interval_separate used capacity (table + BitVec.ofNat 64 offset) aligned bounded (Or.inl before)
    exact frame _ (fun byte inside => (separate byte inside).1) (fun byte inside => (separate byte inside).2)
  have headerRun := evaluate_htabGrow_header zeroed table capacity keys values used order orderPos continuation
    (by rw [locals]; exact tableLocal)
    (by rw [locals]; exact ncapLocal)
    (by rw [locals]; exact nkeysLocal)
    (by rw [locals]; exact nvalsLocal)
    (by rw [locals]; exact nusedLocal)
    (by rw [locals]; exact norderLocal)
    (by rw [locals]; exact norder_posLocal)
    (by rw [addresses]; exact headerDomain 16 (by decide))
    (by rw [addresses]; exact headerDomain 32 (by decide))
    (by rw [addresses]; exact headerDomain 40 (by decide))
    (by rw [addresses]; exact headerDomain 48 (by decide))
    (by rw [addresses]; exact headerDomain 56 (by decide))
    (by rw [addresses]; exact headerDomain 64 (by decide))
    (by rw [addresses]; exact headerDomain 24 (by decide))
  let ready := {zeroed with memory := (htabGrowHeaderPost zeroed table capacity keys values used order orderPos).memory}
  rw [htabGrowHeaderPost_state] at headerRun
  obtain ⟨c16,c32,c40,c48,c56,c64,c24,c0,c8⟩ := htabGrowHeaderPost_fields zeroed table capacity keys values used order orderPos
  have preserved0 : zeroed.memory (table + 0) = state.memory (table + 0) := protectedHeaders 0 (by decide)
  have preserved8 : zeroed.memory (table + 8) = state.memory (table + 8) := protectedHeaders 8 (by decide)
  refine ⟨ready,?_,?_,cost,remaining,locals,globals,postCode,addresses,endian,c0.trans preserved0,c8.trans preserved8,
    c16,c24,c32,c40,c48,c56,c64,?_⟩
  · unfold hashGrowZeroHeader
    rw [evaluateHOLFiniteState_seq_line780,zeroRun]
    exact headerRun
  · have counts := htabGrow_header_preserves_occupancy zeroed table capacity keys values used order orderPos aligned headerBefore bounded
    rw [htabGrowHeaderPost_state] at counts
    exact counts.trans empty
  · intro watched lower upper
    have separate := memcpy_interval_separate used capacity watched aligned bounded (Or.inl upper)
    have preserved := frame watched (fun byte inside => (separate byte inside).1) (fun byte inside => (separate byte inside).2)
    exact (htabGrowHeaderPost_outside zeroed table capacity keys values used order orderPos watched (by omega) lower).trans preserved

#print axioms evaluate_htabGrow_zero_header_outside
end InitECandidate.Runtime
