import InitECandidate.Runtime.HashNewZero
import InitECandidate.Runtime.HashNewSafePlanSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A safe actual allocation plan suffices for occupancy clearing and its
empty-table invariant; no conservative whole-constructor reserve is needed. -/
theorem evaluate_htabNew_zero_prefix_of_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keyLength capacity : BitVec 64) (continuation : ProgHOL 64)
    (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 1 ≤ state.clock)
    (pointerBound : table.toNat ≤ 33806089496) (tableAligned : table.toNat % 8 = 0)
    (safe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity))
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
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "used"),.var .local (ofString "cap")] =
        some [.val (.word (htabNewUsed table keyLength capacity)),.val (.word capacity)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,usedLocal,capLocal]
  have safeCopy := safe
  obtain ⟨_,_,_,keysFinish,valuesRequest,valuesFinish,usedRequest,_⟩ := safeCopy
  have usedEnd := allocationGuard_sum_bound (htabNewUsed table keyLength capacity) capacity valuesFinish usedRequest
  have valuesBound := allocationGuard_sum_bound _ _ keysFinish valuesRequest
  have usedAligned := (allocationEnd_covers _ _ valuesBound).2.2
  change (htabNewUsed table keyLength capacity).toNat % 8 = 0 at usedAligned
  obtain ⟨post,run,_,cost,remaining,globals,postCode,domain,endian,locals,empty⟩ :=
    evaluate_memzero_aligned_call state _ _ (htabNewUsed table keyLength capacity) capacity arguments code ticks
      usedEnd usedAligned wordDomain byteDomain
  have t : post.locals.lookup (ofString "t") = some (.val (.word table)) := by rw [locals]; exact tableLocal
  have u : post.locals.lookup (ofString "used") = some (.val (.word (htabNewUsed table keyLength capacity))) := by
    rw [locals]; exact usedLocal
  have store := evaluate_store_word post (table + 48) (htabNewUsed table keyLength capacity)
    _ (.var .local (ofString "used")) (eval_hashLocalAddress post (ofString "t") table 48 t) u
    (by rw [domain]; exact headerDomain)
  let ready := sourceWriteWord post (table + 48) (htabNewUsed table keyLength capacity)
  refine ⟨ready,?_,?_,?_,cost,remaining,locals,globals,postCode,domain,endian⟩
  · unfold htabNewZeroPrefix
    rw [evaluateHOLFiniteState_seq_line780,run]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,store]
  · change hashOccupiedCount capacity (hashOccupancyRead
      (sourceWriteWord post (table + BitVec.ofNat 64 48) _) _) = 0
    rw [htabNew_header_store_preserves_count_of_safe_plan post table keyLength capacity _ pointerBound tableAligned safe 48 (by decide)]
    exact empty
  · simp [ready,sourceWriteWord]

#print axioms evaluate_htabNew_zero_prefix_of_safe_plan
end InitECandidate.Runtime
