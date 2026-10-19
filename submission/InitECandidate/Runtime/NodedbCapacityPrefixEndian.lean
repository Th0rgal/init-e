import InitECandidate.Runtime.NodedbCapacityPrefixReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem nodedb_capacity_prefix_endian_reaches {F : Type} (state : PanSemStateFiniteExact 64 F) (count : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (small : count.toNat ≤ 134217712) (budget : 2 * count.toNat + 2 ≤ state.clock) :
    Reaches state (nodedbAt 0)
      (fun post =>
        (∃ capacity : BitVec 64, post.locals.lookup (ofString "cap") = some (.val (.word capacity)) ∧
          2 * count.toNat + 2 ≤ capacity.toNat ∧ capacity.toNat ≤ 536870912 ∧
          (∃ bits : Nat, 2 ≤ bits ∧ capacity.toNat = 2^bits)) ∧
        post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
        post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
        (∀ key : MlS, key ≠ ofString "cap" → post.locals.lookup key = state.locals.lookup key))
      (2 * count.toNat + 2) (nodedbAt 2) := by
  let initialized := setVarHOLFinite (ofString "cap") (.val (.word (4#64))) state
  have declaration : Reaches state (nodedbAt 0) (fun next => next = initialized) 0 (nodedbAt 1) := by
    rw [source_nodedb_capacity_declaration]
    apply reaches_dec
    intro value evaluated
    have same : value = .val (.word (4#64)) := by simpa [evalHOLExact] using evaluated.symm
    subst value
    exact ⟨4,rfl,rfl⟩
  have capLocal : initialized.locals.lookup (ofString "cap") = some (.val (.word (4#64))) := by
    simp [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have countLocal : initialized.locals.lookup (ofString "n") = some (.val (.word count)) := by
    simpa (config := {decide := true}) [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atCount
  have bounded := runBounded_nodedb_capacity_loop initialized count code capLocal countLocal small budget
  apply reaches_mono state (nodedbAt 0) (nodedbAt 2) _ _
    (0 + (2 * count.toNat + 2)) (2 * count.toNat + 2) (by omega) (fun _ h => h)
  apply reaches_trans state (nodedbAt 0) (nodedbAt 1) (nodedbAt 2) _ _ 0 (2 * count.toNat + 2) declaration
  intro next same
  subst next
  rw [source_nodedb_capacity]
  apply runBounded_seq_reaches initialized nodedbCapacityLoop (nodedbAt 2) _ _ bounded
  · intro value
    exact evaluate_noDirectReturnWhile nodedbCapacityLoop (by decide) initialized value
  · intro post run
    obtain ⟨capacity,_,memory,globals,installed,domain⟩ :=
      nodedb_capacity_loop_normal_result initialized post count code capLocal countLocal small budget run
    have metadata := evaluateHOLFiniteState_metadata initialized nodedbCapacityLoop
    rw [run] at metadata
    refine ⟨capacity,memory,globals,installed,domain,metadata.2.2.1,?_⟩
    intro key different
    have avoids : avoidsLocal key nodedbCapacityLoop = true := by
      simp [nodedbCapacityLoop,nodedbCapacityBody,avoidsLocal,Ne.symm different]
    have kept := evaluate_avoidsLocal_flowing key nodedbCapacityLoop avoids initialized (by rw [run]; exact Or.inl rfl)
    rw [run] at kept
    rw [kept]
    simp [initialized,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms nodedb_capacity_prefix_endian_reaches
end InitECandidate.Runtime
