import InitECandidate.Runtime.NodedbConstructorTotalBound
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def nodedbTailCost (total : BitVec 64) : Nat :=
  536870912 + 40 + 1 + total.toNat * (nodedbIterationCost (536870912#64) total + 1)
def nodedbBodyCost (total : BitVec 64) : Nat := 2 * total.toNat + 2 + nodedbTailCost total

theorem nodedb_constructor_cost_le (capacity total : BitVec 64) (small : capacity.toNat ≤ 536870912) :
    capacity.toNat + 40 + 1 + total.toNat * (nodedbIterationCost capacity total + 1) ≤ nodedbTailCost total := by
  have mono := setBodyCost_mono 32 capacity (536870912#64) total total (by change _ ≤ 536870912; exact small)
    (le_refl _) (by decide)
  have iter : nodedbIterationCost capacity total ≤ nodedbIterationCost (536870912#64) total := by
    unfold nodedbIterationCost; omega
  have mul := Nat.mul_le_mul_left total.toNat (Nat.add_le_add_right iter 1)
  unfold nodedbTailCost
  omega

theorem source_nodedb_body : sourceFunctionBody Guest.guestFn_nodedb_build = nodedbAt 0 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The complete original database builder has a finite all-outcome bound from
the decoded input geometry, with no assumption of successful allocation/hash. -/
theorem runBounded_nodedb_body {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer total array statePad pad output : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word total)))
    (atArray : s.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (small : total.toNat ≤ 134217712)
    (outputAligned : output.toNat % 8 = 0)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ pointer.toNat)
    (stateEnd : statePad.toNat + 200 ≤ array.toNat) (padEnd : pad.toNat + 136 ≤ array.toNat)
    (outputEnd : output.toNat + 32 ≤ array.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (slices : ∀ j : BitVec 64, j.toNat < total.toNat → ∃ source size : BitVec 64,
      s.memaddrs (array + j * (16#64)) ∧ s.memaddrs (array + j * (16#64) + (8#64)) ∧
      s.memory (array + j * (16#64)) = .word source ∧ s.memory (array + j * (16#64) + (8#64)) = .word size ∧
      size.toNat ≤ 134217712)
    (budget : nodedbBodyCost total ≤ s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn_nodedb_build) (nodedbBodyCost total) := by
  have prefixRun := nodedb_capacity_prefix_reaches s total code atTotal small (by unfold nodedbBodyCost at budget; omega)
  rw [source_nodedb_body]
  unfold RunBounded nodedbBodyCost
  refine evaluate_reaches_terminal_bounded s (nodedbAt 0) (nodedbAt 2) _
    (2 * total.toNat + 2) (nodedbTailCost total) budget prefixRun ?_
  intro next ready remaining
  obtain ⟨⟨capacity,atCap,margin,capacitySmall,bits,lower,power⟩,memory,globals,installed,domain,locals⟩ := ready
  have cost := nodedb_constructor_cost_le capacity total capacitySmall
  have bounded := runBounded_nodedb_constructor_total next pointer capacity total array statePad pad output bits
    (installed.trans code) atCap (by rw [globals]; exact atHeap) aligned capped power
    ((locals _ (by decide)).trans atTotal) ((locals _ (by decide)).trans atArray)
    (by rw [globals]; exact atState) (by rw [globals]; exact atPad) (by rw [globals]; exact atOutput)
    small capacitySmall margin outputAligned arrayEnd stateEnd padEnd outputEnd
    (by intro a h1 h2 h3; rw [domain]; exact arena a h1 h2 h3)
    (by
      intro j inside
      obtain ⟨src,len,sd,ld,sc,lc,sizeSmall⟩ := slices j inside
      refine ⟨src,len,?_,?_,?_,?_,sizeSmall⟩
      · rw [domain]; exact sd
      · rw [domain]; exact ld
      · rw [memory]; exact sc
      · rw [memory]; exact lc)
    (cost.trans remaining)
  exact bounded.weaken cost

#print axioms nodedb_constructor_cost_le
#print axioms runBounded_nodedb_body
end InitECandidate.Runtime
