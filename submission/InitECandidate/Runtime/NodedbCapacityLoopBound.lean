import InitECandidate.Runtime.RankedWhile
import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.StatelessAt22
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def nodedbAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_nodedb_build)
def nodedbCapacityCondition : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "cap"))
    (.op .add [.panop .mul [.const 2,.var .local (ofString "n")],.const 2])
def nodedbCapacityBody : ProgHOL 64 :=
  .assign .local (ofString "cap") (.panop .mul [.var .local (ofString "cap"),.const 2])
def nodedbCapacityLoop : ProgHOL 64 := .while nodedbCapacityCondition nodedbCapacityBody

theorem source_nodedb_capacity : nodedbAt 1 = .seq nodedbCapacityLoop (nodedbAt 2) := rfl

def NodedbCapacityRank (count : BitVec 64) {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat) : Prop :=
  ∃ capacity : BitVec 64,
    state.locals.lookup (ofString "cap") = some (.val (.word capacity)) ∧
    state.locals.lookup (ofString "n") = some (.val (.word count)) ∧
    0 < capacity.toNat ∧ capacity.toNat ≤ 536870912 ∧ (∃ bits : Nat, 2 ≤ bits ∧ capacity.toNat = 2^bits) ∧ rank = (2 * count.toNat + 2) - capacity.toNat

theorem eval_nodedb_capacity_condition {F : Type} (state : PanSemStateFiniteExact 64 F) (capacity count : BitVec 64)
    (atCap : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (small : count.toNat ≤ 134217712) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) nodedbCapacityCondition =
      some (.val (.word (if capacity.toNat < 2 * count.toNat + 2 then 1 else 0))) := by
  have mulNat : ((2#64) * count).toNat = 2 * count.toNat := by
    rw [BitVec.toNat_mul]
    change (2 * count.toNat) % 2^64 = 2 * count.toNat
    apply Nat.mod_eq_of_lt
    omega
  have targetNat : ((2#64) * count + (2#64)).toNat = 2 * count.toNat + 2 := by
    rw [BitVec.toNat_add,mulNat]
    change (2 * count.toNat + 2) % 2^64 = 2 * count.toNat + 2
    apply Nat.mod_eq_of_lt
    omega
  simp [evalHOLFinite_eq_toExact,nodedbCapacityCondition,evalHOLExact,evalListHOLExact,atCap,atCount,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,targetNat]

/-- The actual capacity loop has a finite rank under the decoded input-count cap.
Its arithmetic cannot wrap: an active capacity is less than `2*n+2 < 2^28`. -/
theorem nodedb_capacity_loop_ranked (count : BitVec 64) (small : count.toNat ≤ 134217712) :
    ∀ rank : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      NodedbCapacityRank count state rank → rank ≤ state.clock →
      RankedOutcome state nodedbCapacityCondition rank (NodedbCapacityRank count) False
        (evaluateHOLFiniteState state nodedbCapacityLoop) := by
  have exit : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), NodedbCapacityRank count state 0 →
      ∀ w : BitVec 64, evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) nodedbCapacityCondition =
        some (.val (.word w)) → w = 0 := by
    intro F state ⟨capacity,atCap,atCount,positive,bounded,power,rank⟩ w cond
    rw [eval_nodedb_capacity_condition state capacity count atCap atCount small] at cond
    have no : ¬ capacity.toNat < 2 * count.toNat + 2 := by omega
    simpa [no] using cond.symm
  have step : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (rank : Nat) (w : BitVec 64),
      state.code = originalRuntimeCode → NodedbCapacityRank count state (rank + 1) →
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) nodedbCapacityCondition = some (.val (.word w)) →
      w ≠ 0 → 0 + 1 ≤ state.clock →
      state.clock - 1 ≤ (evaluateHOLFiniteState (decClockHOLFinite state) nodedbCapacityBody).2.clock + 0 ∧
      (evaluateHOLFiniteState (decClockHOLFinite state) nodedbCapacityBody).2.clock ≤ state.clock - 1 ∧
      (evaluateHOLFiniteState (decClockHOLFinite state) nodedbCapacityBody).1 ≠ some .timeOut ∧
      ((evaluateHOLFiniteState (decClockHOLFinite state) nodedbCapacityBody).1 = none ∨
        (evaluateHOLFiniteState (decClockHOLFinite state) nodedbCapacityBody).1 = some .continue →
        ∃ m, m ≤ rank ∧ NodedbCapacityRank count (evaluateHOLFiniteState (decClockHOLFinite state) nodedbCapacityBody).2 m ∧
          (evaluateHOLFiniteState (decClockHOLFinite state) nodedbCapacityBody).2.code = state.code) ∧
      ((evaluateHOLFiniteState (decClockHOLFinite state) nodedbCapacityBody).1 = some .break → False ∧
        ∃ m, NodedbCapacityRank count (evaluateHOLFiniteState (decClockHOLFinite state) nodedbCapacityBody).2 m ∧
          (evaluateHOLFiniteState (decClockHOLFinite state) nodedbCapacityBody).2.code = state.code) := by
    intro F state rank w code ⟨capacity,atCap,atCount,positive,bounded,power,ranking⟩ cond nz budget
    have active : capacity.toNat < 2 * count.toNat + 2 := by omega
    have doubleNat : (capacity * (2#64)).toNat = capacity.toNat * 2 := by
      rw [BitVec.toNat_mul]
      change (capacity.toNat * 2) % 2^64 = capacity.toNat * 2
      apply Nat.mod_eq_of_lt
      omega
    have body : evaluateHOLFiniteState (decClockHOLFinite state) nodedbCapacityBody =
        (none,setVarHOLFinite (ofString "cap") (.val (.word (capacity * (2#64)))) (decClockHOLFinite state)) := by
      simp [nodedbCapacityBody,evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atCap,wordOpHOL,
        wordOp,panOpHOL,valueIsWord,valueWord,isValidValueHOLFinite,lookupKvarHOLFinite,shapeOfHOLExact,shapeEqHOL,
        decClockHOLFinite,setKvarHOLFinite,setVarHOLFinite]
    rw [body]
    refine ⟨by rfl,by rfl,by simp,?_,by simp⟩
    intro _
    refine ⟨(2 * count.toNat + 2) - (capacity * (2#64)).toNat,?_,?_,rfl⟩
    · rw [doubleNat]; omega
    · refine ⟨capacity * (2#64),?_,?_,?_,?_,?_,rfl⟩
      · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      · simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,decClockHOLFinite] using atCount
      · rw [doubleNat]; omega
      · rw [doubleNat]; omega
      · obtain ⟨bits,lower,eq⟩ := power
        exact ⟨bits + 1,(by omega),(by rw [doubleNat,eq,Nat.pow_succ])⟩
  intro rank F state code valid budget
  simpa only [Nat.zero_add,Nat.mul_one,nodedbCapacityLoop] using
    rankedWhile_run nodedbCapacityCondition nodedbCapacityBody 0 (NodedbCapacityRank count) False exit step rank state code valid (by simpa using budget)

#print axioms eval_nodedb_capacity_condition
#print axioms nodedb_capacity_loop_ranked
end InitECandidate.Runtime
