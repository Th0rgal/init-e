import InitECandidate.Runtime.NodedbCapacityLoopBound
import InitECandidate.Runtime.ReadOnlyMemory
import InitECandidate.Runtime.ReadOnlyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Starting at the actual `cap = 4`, the node-database capacity loop is bounded
uniformly by the decoded input-size cap. -/
theorem runBounded_nodedb_capacity_loop {F : Type} (state : PanSemStateFiniteExact 64 F) (count : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (atCap : state.locals.lookup (ofString "cap") = some (.val (.word (4#64))))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (small : count.toNat ≤ 134217712) (budget : 2 * count.toNat + 2 ≤ state.clock) :
    RunBounded state nodedbCapacityLoop (2 * count.toNat + 2) := by
  have valid : NodedbCapacityRank count state ((2 * count.toNat + 2) - 4) :=
    ⟨4,atCap,atCount,(by decide),(by decide),⟨2,(by decide),rfl⟩,rfl⟩
  obtain ⟨spent,remaining,safe,_⟩ := nodedb_capacity_loop_ranked count small _ state code valid (by omega)
  exact ⟨by omega,remaining,safe⟩

theorem nodedb_capacity_loop_normal_result {F : Type} (state post : PanSemStateFiniteExact 64 F) (count : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (atCap : state.locals.lookup (ofString "cap") = some (.val (.word (4#64))))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (small : count.toNat ≤ 134217712) (budget : 2 * count.toNat + 2 ≤ state.clock)
    (run : evaluateHOLFiniteState state nodedbCapacityLoop = (none,post)) :
    (∃ capacity : BitVec 64, post.locals.lookup (ofString "cap") = some (.val (.word capacity)) ∧
      2 * count.toNat + 2 ≤ capacity.toNat ∧ capacity.toNat ≤ 536870912 ∧ (∃ bits : Nat, 2 ≤ bits ∧ capacity.toNat = 2^bits)) ∧
      post.locals.lookup (ofString "n") = some (.val (.word count)) ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs := by
  have valid : NodedbCapacityRank count state ((2 * count.toNat + 2) - 4) :=
    ⟨4,atCap,atCount,(by decide),(by decide),⟨2,(by decide),rfl⟩,rfl⟩
  have outcome := nodedb_capacity_loop_ranked count small _ state code valid (by omega)
  rw [run] at outcome
  obtain ⟨rank,⟨capacity,capLocal,countLocal,positive,bounded,power,ranking⟩,postCode,exit⟩ := outcome.2.2.2 rfl
  have zero : evalHOLFinite post (h := fun a => Classical.propDecidable (post.memaddrs a)) nodedbCapacityCondition =
      some (.val (.word 0)) := by rcases exit with zero | impossible; exact zero; exact impossible.elim
  rw [eval_nodedb_capacity_condition post capacity count capLocal countLocal small] at zero
  have enough : 2 * count.toNat + 2 ≤ capacity.toNat := by
    by_cases lt : capacity.toNat < 2 * count.toNat + 2
    · simp [lt] at zero
    · omega
  have memory := evaluate_readOnly_memory nodedbCapacityLoop (by rfl) state
  have globals := evaluate_readOnly_globals nodedbCapacityLoop (by rfl) state
  have metadata := evaluateHOLFiniteState_metadata state nodedbCapacityLoop
  rw [run] at memory globals metadata
  exact ⟨⟨capacity,capLocal,enough,bounded,power⟩,countLocal,memory,globals,postCode,metadata.2.1⟩

#print axioms runBounded_nodedb_capacity_loop
#print axioms nodedb_capacity_loop_normal_result
end InitECandidate.Runtime
