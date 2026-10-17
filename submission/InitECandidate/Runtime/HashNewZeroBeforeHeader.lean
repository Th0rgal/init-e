import InitECandidate.Runtime.HashNewZeroFrame
import InitECandidate.Runtime.HashNewLayout
import InitECandidate.Runtime.MemzeroAlignedCombinedCall
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Occupancy initialization preserves every memory cell before the new table header. -/
theorem evaluate_htabNew_zero_prefix_before_header {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 1 ≤ state.clock)
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word (htabNewUsed table keyLength capacity))))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (headerDomain : state.memaddrs (table + 48))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat →
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset))) :
    ∃ ready, evaluateHOLFiniteState state (htabNewZeroPrefix continuation) = evaluateHOLFiniteState ready continuation ∧
      hashOccupiedCount capacity (hashOccupancyRead ready (htabNewUsed table keyLength capacity)) = 0 ∧
      ready.memory (table + 48) = .word (htabNewUsed table keyLength capacity) ∧
      state.clock ≤ ready.clock + capacity.toNat + 1 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧
      ∀ address : BitVec 64, address.toNat < table.toNat →
        ready.memory address = state.memory address := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "used"),.var .local (ofString "cap")] =
        some [.val (.word (htabNewUsed table keyLength capacity)),.val (.word capacity)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,usedLocal,capLocal]
  have bounds := htabNew_used_bounds table keyLength capacity keyBound tableAligned budget
  obtain ⟨post,run,_,cost,remaining,globals,postCode,domain,endian,locals,empty,frame⟩ :=
    evaluate_memzero_aligned_call_with_frame state _ _ (htabNewUsed table keyLength capacity) capacity arguments code ticks
      bounds.1 bounds.2 wordDomain byteDomain
  have t : post.locals.lookup (ofString "t") = some (.val (.word table)) := by rw [locals]; exact tableLocal
  have u : post.locals.lookup (ofString "used") = some (.val (.word (htabNewUsed table keyLength capacity))) := by
    rw [locals]; exact usedLocal
  have store := evaluate_store_word post (table + 48) (htabNewUsed table keyLength capacity)
    _ (.var .local (ofString "used")) (eval_hashLocalAddress post (ofString "t") table 48 t) u
    (by rw [domain]; exact headerDomain)
  let ready := sourceWriteWord post (table + 48) (htabNewUsed table keyLength capacity)
  refine ⟨ready,?_,?_,?_,cost,remaining,locals,globals,postCode,domain,endian,?_⟩
  · unfold htabNewZeroPrefix
    rw [evaluateHOLFiniteState_seq_line780,run]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,store]
  · change hashOccupiedCount capacity (hashOccupancyRead
      (sourceWriteWord post (table + BitVec.ofNat 64 48) _) _) = 0
    rw [htabNew_header_store_preserves_count post table keyLength capacity _ keyBound tableAligned budget 48 (by decide)]
    exact empty
  · simp [ready,sourceWriteWord]

  · intro address before
    have layout := htabNew_insertion_layout table keyLength capacity keyBound budget
    dsimp only at layout
    have address48 : (table + (48 : BitVec 64)).toNat = table.toNat + 48 := by
      rw [BitVec.toNat_add_of_lt (by change table.toNat + 48 < 2 ^ 64; omega)]
      rfl
    have separate : address ≠ table + 48 := by
      intro same
      have equal := congrArg BitVec.toNat same
      rw [address48] at equal
      omega
    have outside : address.toNat < (htabNewUsed table keyLength capacity).toNat := by omega
    have protectedWord := memcpy_interval_separate (htabNewUsed table keyLength capacity) capacity
      address bounds.2 bounds.1 (Or.inl outside)
    change (sourceWriteWord post (table + 48) _).memory address = _
    simp only [sourceWriteWord,if_neg separate]
    exact frame _ (fun byte inside => (protectedWord byte inside).1)
      (fun byte inside => (protectedWord byte inside).2)

#print axioms evaluate_htabNew_zero_prefix_before_header
end InitECandidate.Runtime
