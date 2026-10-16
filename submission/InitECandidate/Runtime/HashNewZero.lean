import InitECandidate.Runtime.HashNewSeparation
import InitECandidate.Runtime.MemzeroAlignedCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The constructor's occupancy allocation has an aligned start and fits the
heap, as required by the actual memzero evaluator theorem. -/
theorem htabNew_used_bounds (table keyLength capacity : BitVec 64)
    (keyBound : keyLength.toNat ≤ 52) (tableAligned : table.toNat % 8 = 0)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496) :
    (htabNewUsed table keyLength capacity).toNat + capacity.toNat ≤ 33806089496 ∧
      (htabNewUsed table keyLength capacity).toNat % 8 = 0 := by
  have plan := (htabNew_allocation_plan_safe table keyLength capacity keyBound budget).1
  obtain ⟨g1,b1,g2,b2,g3,b3,g4,_,_⟩ := plan
  have prefixSafe : AllocationPlanSafe table
      [72,capacity * allocationEnd 0 keyLength,capacity * 8] := ⟨g1,b1,g2,b2,g3,b3,b3⟩
  have facts := allocationPlan_facts _ table prefixSafe (by omega) tableAligned
  exact ⟨allocationGuard_sum_bound (htabNewUsed table keyLength capacity) capacity b3 g4,facts.2.2⟩

def htabNewZeroPrefix (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "memzero")
      [.var .local (ofString "used"),.var .local (ofString "cap")])
    (.seq (.store (hashLocalAddress (ofString "t") 48) (.var .local (ofString "used"))) continuation)

def htabNewUsedBody : ProgHOL 64 :=
  match htabNewAfterHeader with
  | .decCall _ _ _ _ (.seq _ (.decCall _ _ _ _ (.seq _ (.decCall _ _ _ _ body)))) => body
  | _ => .skip

def htabNewAfterZero : ProgHOL 64 :=
  match htabNewUsedBody with | .seq _ (.seq _ rest) => rest | _ => .skip

/-- The fragment is the literal body of the original used-allocation scope. -/
theorem source_htabNew_zero_prefix : htabNewUsedBody = htabNewZeroPrefix htabNewAfterZero := by
  rfl

/-- Occupancy initialization and its following pointer store spend at most
capacity+1 source clocks and reach the continuation with an empty table. -/
theorem evaluate_htabNew_zero_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "used"),.var .local (ofString "cap")] =
        some [.val (.word (htabNewUsed table keyLength capacity)),.val (.word capacity)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,usedLocal,capLocal]
  have bounds := htabNew_used_bounds table keyLength capacity keyBound tableAligned budget
  obtain ⟨post,run,_,cost,remaining,globals,postCode,domain,endian,locals,empty⟩ :=
    evaluate_memzero_aligned_call state _ _ (htabNewUsed table keyLength capacity) capacity arguments code ticks
      bounds.1 bounds.2 wordDomain byteDomain
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
    rw [htabNew_header_store_preserves_count post table keyLength capacity _ keyBound tableAligned budget 48 (by decide)]
    exact empty
  · simp [ready,sourceWriteWord]

#print axioms source_htabNew_zero_prefix
#print axioms htabNew_used_bounds
#print axioms evaluate_htabNew_zero_prefix
end InitECandidate.Runtime
