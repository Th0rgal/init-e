import InitECandidate.Runtime.AccessListKeysLoopBound
import InitECandidate.Runtime.AccessListKeysOtherLocal
import InitECandidate.Runtime.AccessListKeysLoopHeapInvariant
import InitECandidate.Runtime.AccessListStepControl
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original access-list key traversal has an explicit input-dependent clock
bound, including memory failures and exceptions from field validation. -/
theorem evaluate_access_keys_loop_heap_local_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (key : MlS) (different : key ≠ ofString "j") (notScoped : key ≠ ofString "k")
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessKeysLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : (count.toNat - valid.index.toNat) *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state accessKeysLoop = (result,post) ∧
      state.clock ≤ post.clock + (count.toNat - valid.index.toNat) *
        (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ next : AccessKeysLoopWitness post array count buffer input inputLength scratch frame ceiling,
        next.index = count ∧ post.locals.lookup key = state.locals.lookup key) ∧ (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    Nonempty (AccessKeysLoopWitness current array count buffer input inputLength scratch frame ceiling) ∧
      current.locals.lookup key = state.locals.lookup key
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92650
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ witness : AccessKeysLoopWitness current array count buffer input inputLength scratch frame ceiling,
      accessKeysRank count current = count.toNat - witness.index.toNat := by
    intro current witness
    simp [accessKeysRank,witness.indexLocal]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a))
      (.cmp .lower (.var .local (ofString "j")) (.rfield 1 (.var .local (ofString "slots")))) =
      some (.val (.word (if accessKeysRank count current = 0 then 0 else 1))) := by
    rintro current ⟨⟨witness⟩,kept⟩
    by_cases inside : witness.index.toNat < count.toNat
    · have nonzero : accessKeysRank count current ≠ 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,nonzero]
    · have zero : accessKeysRank count current = 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨⟨witness⟩,kept⟩; exact ⟨⟨witness.decClock⟩,kept⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      accessKeysRank count (decClockHOLFinite current) = accessKeysRank count current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < accessKeysRank count current → cost ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + cost ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current accessKeysStep = (none,post) ∧ invariant post ∧
          accessKeysRank count post < accessKeysRank count current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current accessKeysStep = (some result,post))) := by
    rintro current ⟨⟨witness⟩,kept⟩ positive ticks
    have inside : witness.index.toNat < count.toNat := by rw [rankEq current witness] at positive; omega
    have bounded := evaluate_access_keys_step_bounded current array count witness.index buffer input inputLength scratch frame ceiling inputLimit
      witness.listLocal witness.bufferLocal witness.indexLocal witness.slices inside inputBound limitBound witness.scratchGlobal witness.frameGlobal
      witness.code orderedFrame framePositive scratchBelow witness.arena ticks
    have control := evaluate_access_keys_step_control current
    cases run : evaluateHOLFiniteState current accessKeysStep with
    | mk result post =>
      rw [run] at bounded control
      refine ⟨post,bounded.1,bounded.2.1,?_⟩
      cases result with
      | none =>
        obtain ⟨next,decreases⟩ := access_keys_loop_heap_witness_step current post array count buffer input inputLength scratch frame ceiling inputLimit
          witness inside inputBound limitBound orderedFrame framePositive scratchBelow arrayAbove arrayBeforeBuffer aligned fits ticks run
        have same := access_keys_step_normal_other_local current post witness.index count array key different notScoped
          witness.indexLocal witness.listLocal run
        exact Or.inl ⟨rfl,⟨⟨next⟩,same.trans kept⟩,by rw [rankEq post next,rankEq current witness]; exact decreases⟩
      | some result =>
        refine Or.inr ⟨result,?_,?_,?_,?_,rfl⟩
        · intro equal; subst result; exact control.2.1 rfl
        · intro equal; subst result; exact bounded.2.2 rfl
        · intro equal; subst result; exact control.1 rfl
        · intro value equal; subst result; exact control.2.2 value rfl
  obtain ⟨result,post,run,total,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .lower (.var .local (ofString "j")) (.rfield 1 (.var .local (ofString "slots")))) accessKeysStep
    invariant (accessKeysRank count) cost guard enter entryRank step state ⟨⟨valid⟩,rfl⟩
    (by simpa only [rankEq state valid,cost] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · rw [source_access_keys_loop]; exact run
  · simpa only [rankEq state valid,cost] using total
  · intro normal
    obtain ⟨⟨⟨next⟩,kept⟩,zero⟩ := done normal
    refine ⟨next,?_,kept⟩
    apply BitVec.eq_of_toNat_eq
    rw [rankEq post next] at zero
    have bounded := next.indexBound
    omega

#print axioms evaluate_access_keys_loop_heap_local_bounded
theorem access_keys_loop_normal_heap_other_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (different : key ≠ ofString "j") (notScoped : key ≠ ofString "k")
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessKeysLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : (count.toNat - valid.index.toNat) *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock)
    (run : evaluateHOLFiniteState state accessKeysLoop = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  obtain ⟨result,output,evaluated,_,_,_,done,_⟩ := evaluate_access_keys_loop_heap_local_bounded state key different notScoped
    array count buffer input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayAbove arrayBeforeBuffer aligned fits budget
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (evaluated.symm.trans run)
  obtain ⟨next,_,kept⟩ := done rfl
  exact kept

#print axioms access_keys_loop_normal_heap_other_local
end InitECandidate.Runtime
