import InitECandidate.Runtime.NodedbLoopResult
import InitECandidate.Runtime.NoLoopControl
/-!
Memory windows of the real node-database builder (insertion loop).

`nodedb_insertion_normal_frame` shows that one complete insertion iteration only
writes inside the hash state/pad/output windows and the growing table, so every
word below the table base and outside those three windows is untouched.  This
module restates that as `NodedbProtected`-shaped frame facts and carries them
through the actual insertion loop on a normal exit: a protected word is never
written by any number of iterations, no matter how many entries are inserted,
and a normal exit drops no mapped address.

Scope: these are the loop-level facts of the returned frame.  The body-level
composition (capacity declaration and loop, table constructor, final return)
still has to be assembled from the corresponding normal-path analyses.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- One normal insertion iteration never writes a protected word: a word below
the table base and outside the state/pad/output hash windows is unchanged. -/
theorem nodedb_iteration_protected_frame {F : Type} (c : NodedbLoopConfig) (g : NodedbLoopGeometry c)
    (s post : PanSemStateFiniteExact 64 F) (index count heap : BitVec 64)
    (valid : NodedbLoopInv c index count heap s) (active : index.toNat < c.total.toNat)
    (budget : nodedbIterationCost c.capacity c.total ≤ s.clock)
    (run : evaluateHOLFiniteState s nodedbInsertionBody = (none,post))
    (w : BitVec 64) (kept : NodedbProtected c w) :
    post.memory w = s.memory w := by
  obtain ⟨source,size,sourceDomain,sizeDomain,sourceCell,sizeCell,small⟩ := valid.slices index active
  have cost := nodedb_iteration_cost_le c.capacity c.total size count small
    (by have := valid.occupancy; omega) g.capacitySmall
  obtain ⟨_,_,_,_,frame⟩ := nodedb_insertion_normal_frame s post c.pointer c.pad c.array index c.total source size
    c.output heap c.table c.keys c.stride c.capacity c.used c.values c.order c.orderPos count c.bits
    valid.tableInv valid.ordered valid.stateGlobal valid.padGlobal valid.arrayLocal valid.indexLocal
    valid.tableLocal valid.outputGlobal sourceDomain sizeDomain sourceCell sizeCell small g.outputAligned
    valid.heapGlobal valid.heapAligned valid.headerBelow valid.heapInside valid.arena
    (by have := valid.occupancy; have := g.capacityMargin; omega) g.tableSeparate (cost.trans budget)
    g.capacityMargin valid.occupancy active run
  exact frame w kept.1 kept.2.1 kept.2.2.1 kept.2.2.2

/-- The original insertion loop never writes a protected word and never drops a
mapped address: every word below the table base and outside the state/pad/output
hash windows is unchanged after any normal exit, for any number of entries. -/
theorem nodedb_insertion_loop_normal_window {F : Type} (c : NodedbLoopConfig) (g : NodedbLoopGeometry c) :
    ∀ (rank : Nat) (s post : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      NodedbLoopRank c s rank → rank * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock →
      evaluateHOLFiniteState s nodedbInsertionLoop = (none,post) →
      post.memaddrs = s.memaddrs ∧ ∀ w : BitVec 64, NodedbProtected c w → post.memory w = s.memory w := by
  intro rank s post scode ranked budget run
  have main : ∀ n : Nat, ∀ (rank : Nat) (s post : PanSemStateFiniteExact 64 F), s.clock = n →
      s.code = originalRuntimeCode → NodedbLoopRank c s rank →
      rank * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock →
      evaluateHOLFiniteState s nodedbInsertionLoop = (none,post) →
      post.memaddrs = s.memaddrs ∧ ∀ w : BitVec 64, NodedbProtected c w → post.memory w = s.memory w := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro rank s post clock scode ranked budget run
      rw [nodedbInsertionLoop,evaluateHOLFiniteState_while_total] at run
      split at run
      · rename_i v hv
        split at run
        · rename_i nz
          split at run
          · obtain ⟨_,rfl⟩ := run
          · dsimp only at run
            rw [fixClockHOLFinite_evaluateState] at run
            have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite s) nodedbInsertionBody
            cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite s) nodedbInsertionBody with
            | mk rb mid =>
              rw [bodyRun] at run remaining
              obtain ⟨index,count,heap,inv,ranking⟩ := ranked
              have active : index.toNat < c.total.toNat := by
                by_contra inactive
                rw [eval_nodedb_loop_condition s index c.total inv.indexLocal inv.totalLocal,
                  if_neg inactive] at hv
                exact nz (by simpa using hv.symm)
              have entered := inv.decClock
              have rankPos : 0 < rank := by rw [ranking]; omega
              have rankGrowth : nodedbIterationCost c.capacity c.total + 1 ≤
                  rank * (nodedbIterationCost c.capacity c.total + 1) :=
                Nat.le_mul_of_pos_left _ rankPos
              have ticks : nodedbIterationCost c.capacity c.total ≤ (decClockHOLFinite s).clock := by
                change _ ≤ s.clock - 1; omega
              have bounded := nodedb_loop_iteration_bounded c g (decClockHOLFinite s) index count heap
                entered active ticks
              have controls := evaluate_noLoopControl nodedbInsertionBody (by decide) (decClockHOLFinite s)
              have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite s) nodedbInsertionBody
              rw [bodyRun] at meta'
              cases rb with
              | none =>
                obtain ⟨nextCount,nextHeap,nextInv⟩ := nodedb_loop_iteration_preserves c g (decClockHOLFinite s)
                  mid index count heap entered active ticks bodyRun
                have natural : (index + (1#64)).toNat = index.toNat + 1 := word_add_toNat index 1
                  (by have := g.totalSmall; omega)
                have lower : s.clock - 1 ≤ mid.clock + nodedbIterationCost c.capacity c.total := by
                  have h := bounded.1
                  have midEq : (evaluateHOLFiniteState (decClockHOLFinite s) nodedbInsertionBody).2 = mid := by
                    rw [bodyRun]
                  rw [midEq] at h
                  change s.clock - 1 ≤ mid.clock + nodedbIterationCost c.capacity c.total at h
                  exact h
                have nextBudget : (c.total.toNat - (index + (1#64)).toNat) *
                    (nodedbIterationCost c.capacity c.total + 1) ≤ mid.clock := by
                  have hIndex : c.total.toNat - (index + (1#64)).toNat =
                      (c.total.toNat - index.toNat) - 1 := by omega
                  rw [hIndex, Nat.sub_mul, Nat.one_mul]
                  have shrink : (c.total.toNat - index.toNat) *
                      (nodedbIterationCost c.capacity c.total + 1) -
                        (nodedbIterationCost c.capacity c.total + 1) ≤
                      s.clock - (nodedbIterationCost c.capacity c.total + 1) :=
                    Nat.sub_le_sub_right (by rw [← ranking]; exact budget) _
                  refine shrink.trans ?_
                  rw [Nat.sub_le_iff_le_add]
                  omega
                have smaller : mid.clock < n := by
                  change mid.clock ≤ s.clock - 1 at remaining
                  omega
                have recurse := ih mid.clock smaller (c.total.toNat - (index + (1#64)).toNat) mid post rfl
                  (meta'.1.trans scode) ⟨index + (1#64),nextCount,nextHeap,nextInv,rfl⟩ nextBudget run
                refine ⟨recurse.1.trans meta'.2.1, fun w kept => ?_⟩
                exact (recurse.2 w kept).trans (nodedb_iteration_protected_frame c g (decClockHOLFinite s) mid
                  index count heap entered active ticks bodyRun w kept)
              | some rb =>
                simp only [bodyRun] at controls
                cases rb with
                | «continue» => exact absurd rfl controls.2
                | «break» => exact absurd rfl controls.1
                | returned value => dsimp only at run; exact absurd (Prod.mk.inj run).1 (by simp)
                | exception left right => dsimp only at run; exact absurd (Prod.mk.inj run).1 (by simp)
                | finalFfi left => dsimp only at run; exact absurd (Prod.mk.inj run).1 (by simp)
                | error => dsimp only at run; exact absurd (Prod.mk.inj run).1 (by simp)
                | timeOut => dsimp only at run; exact absurd (Prod.mk.inj run).1 (by simp)
        · obtain ⟨rfl,rfl⟩ := run
          exact ⟨rfl,fun _ _ => rfl⟩
      · exact absurd (Prod.mk.inj run).1 (by simp)
  exact main s.clock rank s post rfl scode ranked budget run

/-- A normal exit of the original insertion loop retains the concrete table, heap
and input invariants, drops no mapped address and never writes a protected word. -/
theorem nodedb_insertion_loop_normal_summary {F : Type} (c : NodedbLoopConfig) (g : NodedbLoopGeometry c)
    (s post : PanSemStateFiniteExact 64 F) (count heap : BitVec 64)
    (valid : NodedbLoopInv c 0 count heap s)
    (budget : c.total.toNat * (nodedbIterationCost c.capacity c.total + 1) ≤ s.clock)
    (run : evaluateHOLFiniteState s nodedbInsertionLoop = (none,post)) :
    ∃ index nextCount nextHeap : BitVec 64, index = c.total ∧
      NodedbLoopInv c index nextCount nextHeap post ∧
      post.memaddrs = s.memaddrs ∧
      ∀ w : BitVec 64, NodedbProtected c w → post.memory w = s.memory w := by
  obtain ⟨index,nextCount,nextHeap,nextInv,indexTotal⟩ :=
    nodedb_insertion_loop_normal_result c g s post count heap valid budget run
  have main := nodedb_insertion_loop_normal_window c g c.total.toNat s post valid.tableInv.code
    ⟨0,count,heap,valid,rfl⟩ budget run
  exact ⟨index,nextCount,nextHeap,indexTotal,nextInv,main.1,main.2⟩

#print axioms nodedb_iteration_protected_frame
#print axioms nodedb_insertion_loop_normal_window
#print axioms nodedb_insertion_loop_normal_summary
end InitECandidate.Runtime
