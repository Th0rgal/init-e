import InitECandidate.Runtime.NodedbConstructorLoopEntry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual table constructor and complete remaining source suffix have a
finite all-outcome bound. The normal constructor result establishes the loop
invariant; no caller-supplied tail bound is required. -/
theorem runBounded_nodedb_constructor_total {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer capacity total array statePad pad output : BitVec 64) (bits : Nat)
    (code : s.code = originalRuntimeCode)
    (atCap : s.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (power : capacity.toNat = 2 ^ bits)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word total)))
    (atArray : s.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (small : total.toNat ≤ 134217712) (capacitySmall : capacity.toNat ≤ 536870912)
    (margin : 2 * total.toNat + 2 ≤ capacity.toNat) (outputAligned : output.toNat % 8 = 0)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ pointer.toNat)
    (stateEnd : statePad.toNat + 200 ≤ array.toNat) (padEnd : pad.toNat + 136 ≤ array.toNat)
    (outputEnd : output.toNat + 32 ≤ array.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (slices : ∀ j : BitVec 64, j.toNat < total.toNat → ∃ source size : BitVec 64,
      s.memaddrs (array + j * (16#64)) ∧ s.memaddrs (array + j * (16#64) + (8#64)) ∧
      s.memory (array + j * (16#64)) = .word source ∧ s.memory (array + j * (16#64) + (8#64)) = .word size ∧
      size.toNat ≤ 134217712)
    (budget : capacity.toNat + 40 + 1 + total.toNat * (nodedbIterationCost capacity total + 1) ≤ s.clock) :
    RunBounded s (nodedbAt 2) (capacity.toNat + 40 + 1 + total.toNat * (nodedbIterationCost capacity total + 1)) := by
  apply runBounded_nodedb_constructor s pointer capacity bits (total.toNat * (nodedbIterationCost capacity total + 1))
    code atCap atHeap aligned capped arena power budget
  intro next ready remaining
  obtain ⟨c,totalEq,capacityEq,geometry,heap,valid⟩ := nodedb_constructor_loop_entry s next pointer capacity total array
    statePad pad output bits ready atTotal atArray atState atPad atOutput small capacitySmall margin outputAligned
    arrayEnd stateEnd padEnd outputEnd arena slices
  have bounded := runBounded_nodedb_suffix c geometry next heap valid (by rw [totalEq,capacityEq]; exact remaining)
  rw [totalEq,capacityEq] at bounded
  exact bounded

#print axioms runBounded_nodedb_constructor_total
end InitECandidate.Runtime
