import InitECandidate.Runtime.HashTableReadyMemzero32
import InitECandidate.Runtime.HashTableReadyWordOutside32
import InitECandidate.Runtime.HashNewZero
import InitECandidate.Runtime.HashNewLayout
import InitECandidate.Runtime.MemzeroAlignedCombinedCall
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Occupancy initialization preserves every previously written header field. -/
theorem evaluate_htabNew_zero_prefix_other {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      state.memaddrs (panByteAlignHOL (htabNewUsed table keyLength capacity + BitVec.ofNat 64 offset)))
    (otherTable pointer keys stride otherCapacity used values order orderPos items : BitVec 64) (bits : Nat)
    (otherReady : HashTableReady32 otherTable keys stride otherCapacity used values order orderPos items bits pointer state)
    (outside : (htabNewUsed table keyLength capacity).toNat + capacity.toNat ≤ otherTable.toNat ∨
      orderPos.toNat + otherCapacity.toNat * 8 ≤ (htabNewUsed table keyLength capacity).toNat)
    (headerOutside : (table + 48).toNat < otherTable.toNat ∨ orderPos.toNat + otherCapacity.toNat * 8 ≤ (table + 48).toNat) :
    ∃ ready, evaluateHOLFiniteState state (htabNewZeroPrefix continuation) = evaluateHOLFiniteState ready continuation ∧
      HashTableReady32 otherTable keys stride otherCapacity used values order orderPos items bits pointer ready ∧
      hashOccupiedCount capacity (hashOccupancyRead ready (htabNewUsed table keyLength capacity)) = 0 ∧
      ready.memory (table + 48) = .word (htabNewUsed table keyLength capacity) ∧
      state.clock ≤ ready.clock + capacity.toNat + 1 ∧ ready.clock ≤ state.clock ∧
      ready.locals = state.locals ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be
 := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "used"),.var .local (ofString "cap")] =
        some [.val (.word (htabNewUsed table keyLength capacity)),.val (.word capacity)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,usedLocal,capLocal]
  have bounds := htabNew_used_bounds table keyLength capacity keyBound tableAligned budget
  obtain ⟨post,run,preserved,empty,cost,remaining,globals,postCode,domain,endian,locals⟩ :=
    otherReady.memzero_outside state _ _ (htabNewUsed table keyLength capacity) capacity arguments code ticks
      bounds.1 bounds.2 wordDomain byteDomain otherTable pointer keys stride otherCapacity used values order orderPos items bits outside
  have t : post.locals.lookup (ofString "t") = some (.val (.word table)) := by rw [locals]; exact tableLocal
  have u : post.locals.lookup (ofString "used") = some (.val (.word (htabNewUsed table keyLength capacity))) := by
    rw [locals]; exact usedLocal
  have store := evaluate_store_word post (table + 48) (htabNewUsed table keyLength capacity)
    _ (.var .local (ofString "used")) (eval_hashLocalAddress post (ofString "t") table 48 t) u
    (by rw [domain]; exact headerDomain)
  let ready := sourceWriteWord post (table + 48) (htabNewUsed table keyLength capacity)
  refine ⟨ready,?_,preserved.after_word_outside post otherTable pointer keys stride otherCapacity used values order orderPos items (table + 48) (htabNewUsed table keyLength capacity) bits headerOutside,?_,?_,cost,remaining,locals,globals,postCode,domain,endian⟩
  · unfold htabNewZeroPrefix
    rw [evaluateHOLFiniteState_seq_line780,run]
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780,store]
  · change hashOccupiedCount capacity (hashOccupancyRead
      (sourceWriteWord post (table + BitVec.ofNat 64 48) _) _) = 0
    rw [htabNew_header_store_preserves_count post table keyLength capacity _ keyBound tableAligned budget 48 (by decide)]
    exact empty
  · simp [ready,sourceWriteWord]

#print axioms evaluate_htabNew_zero_prefix_other
end InitECandidate.Runtime
