import InitECandidate.Runtime.AuthorizationsLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- The actual authorization loop has an input-dependent clock bound,
including memory failures and exceptions from record validation. -/
theorem evaluate_authorizations_loop_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AuthorizationsLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 16 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : (count.toNat - valid.index.toNat) *
      (authorizationStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state authorizationLoop = (result,post) ∧
      state.clock ≤ post.clock + (count.toNat - valid.index.toNat) *
        (authorizationStepCost inputLength.toNat inputLength.toNat + 1) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ next : AuthorizationsLoopWitness post array count records input inputLength scratch frame ceiling,
        next.index = count ∧ next.heap.toNat = valid.heap.toNat + 96 * (count.toNat - valid.index.toNat)) ∧ (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F =>
    ∃ witness : AuthorizationsLoopWitness current array count records input inputLength scratch frame ceiling,
      witness.heap.toNat + 96 * (count.toNat - witness.index.toNat) = valid.heap.toNat + 96 * (count.toNat - valid.index.toNat)
  let cost := authorizationStepCost inputLength.toNat inputLength.toNat
  have rankEq : ∀ current : PanSemStateFiniteExact 64 F, ∀ witness : AuthorizationsLoopWitness current array count records input inputLength scratch frame ceiling,
      authorizationRank count current = count.toNat - witness.index.toNat := by
    intro current witness
    simp [authorizationRank,witness.indexLocal]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun a => Classical.propDecidable (current.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) =
      some (.val (.word (if authorizationRank count current = 0 then 0 else 1))) := by
    rintro current ⟨witness,accounting⟩
    by_cases inside : witness.index.toNat < count.toNat
    · have nonzero : authorizationRank count current ≠ 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,nonzero]
    · have zero : authorizationRank count current = 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.listLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨witness,accounting⟩; exact ⟨witness.decClock,accounting⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      authorizationRank count (decClockHOLFinite current) = authorizationRank count current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < authorizationRank count current → cost ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + cost ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current authorizationStep = (none,post) ∧ invariant post ∧
          authorizationRank count post < authorizationRank count current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current authorizationStep = (some result,post))) := by
    rintro current ⟨witness,accounting⟩ positive ticks
    have inside : witness.index.toNat < count.toNat := by rw [rankEq current witness] at positive; omega
    let record := records + witness.index * 120#64
    have recordNat : record.toNat = records.toNat + witness.index.toNat * 120 := by
      have product : (witness.index * 120#64).toNat = witness.index.toNat * 120 := by
        apply BitVec.toNat_mul_of_lt
        have b := witness.recordsBeforeHeap
        have h := witness.heapBound
        change witness.index.toNat * 120 < 2^64
        omega
      dsimp only [record]
      rw [BitVec.toNat_add_of_lt (by rw [product]; have b := witness.recordsBeforeHeap; have h := witness.heapBound; omega),product]
    have recordBeforeHeap : record.toNat + 120 ≤ witness.heap.toNat := by
      rw [recordNat]
      have b := witness.recordsBeforeHeap
      omega
    have heapBeforeFrame : witness.heap.toNat + inputLength.toNat * 16 ≤ frame.toNat := by
      have reserve := witness.reserve
      omega
    have bounded := evaluate_authorization_step_input_bounded current record records witness.index array count input inputLength scratch frame witness.heap
      ceiling inputLimit rfl witness.recordsLocal witness.indexLocal witness.listLocal witness.slices inside inputBound limitBound
      witness.scratchGlobal witness.frameGlobal witness.code orderedFrame framePositive scratchBelow witness.arena witness.heapGlobal
      witness.heapBound countLimit witness.heapArena inputBeforeFrame witness.inputBeforeHeap heapBeforeFrame recordBeforeHeap
      (by have h := witness.heapBound; omega) ticks
    have control := evaluate_authorization_step_control current
    cases run : evaluateHOLFiniteState current authorizationStep with
    | mk result post =>
      rw [run] at bounded control
      refine ⟨post,bounded.1,bounded.2.1,?_⟩
      cases result with
      | none =>
        obtain ⟨next,decreases⟩ := authorizations_loop_witness_step current post array count records input inputLength scratch frame ceiling inputLimit
          witness inside inputBound limitBound orderedFrame framePositive scratchBelow countLimit inputBeforeFrame arrayBeforeFrame arrayBeforeRecords ticks run
        have runtime := authorization_step_input_normal_fixed_heap current post record records witness.index array count input inputLength scratch frame witness.heap
          ceiling inputLimit rfl witness.recordsLocal witness.indexLocal witness.listLocal witness.slices inside inputBound limitBound
          witness.scratchGlobal witness.frameGlobal witness.code orderedFrame framePositive scratchBelow witness.arena witness.heapGlobal
          witness.heapBound countLimit witness.heapArena inputBeforeFrame witness.inputBeforeHeap heapBeforeFrame recordBeforeHeap
          (by have h := witness.heapBound; omega) ticks run
        have sameHeap : next.heap = allocationEnd witness.heap 96 :=
          HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (next.heapGlobal.symm.trans runtime.1)))
        have heapNat := authorization_heap_advance witness.heap runtime.2.2.2.1 witness.heapAligned
        obtain ⟨advanced,indexNat,_⟩ := evaluate_authorization_step_rank_progress current post witness.index count witness.indexLocal inside run
        have sameIndex : next.index = witness.index + 1 :=
          HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (next.indexLocal.symm.trans advanced)))
        have nextAccounting : next.heap.toNat + 96 * (count.toNat - next.index.toNat) =
            valid.heap.toNat + 96 * (count.toNat - valid.index.toNat) := by
          rw [sameHeap,heapNat,sameIndex,indexNat]
          omega
        exact Or.inl ⟨rfl,⟨next,nextAccounting⟩,by rw [rankEq post next,rankEq current witness]; exact decreases⟩
      | some result =>
        refine Or.inr ⟨result,?_,?_,?_,?_,rfl⟩
        · intro equal; subst result; exact control.2.1 rfl
        · intro equal; subst result; exact bounded.2.2 rfl
        · intro equal; subst result; exact control.1 rfl
        · intro value equal; subst result; exact control.2.2 value rfl
  obtain ⟨result,post,run,total,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .lower (.var .local (ofString "i")) (.rfield 1 (.var .local (ofString "lst")))) authorizationStep
    invariant (authorizationRank count) cost guard enter entryRank step state ⟨valid,rfl⟩
    (by simpa only [rankEq state valid,cost] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · rw [source_authorization_loop]; exact run
  · simpa only [rankEq state valid,cost] using total
  · intro normal
    obtain ⟨⟨next,accounting⟩,zero⟩ := done normal
    have equal : next.index = count := by
      apply BitVec.eq_of_toNat_eq
      rw [rankEq post next] at zero
      have bounded := next.indexBound
      omega
    refine ⟨next,equal,?_⟩
    rw [equal] at accounting
    simpa using accounting

#print axioms evaluate_authorizations_loop_heap_bounded
end InitECandidate.Runtime
