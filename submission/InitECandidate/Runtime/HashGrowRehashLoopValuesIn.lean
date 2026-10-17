import InitECandidate.Runtime.HashGrowRehashLoopSupported
import InitECandidate.Runtime.HashGrowRehashBodyValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete actual rehash loop preserves registered-pointer membership
in both the newly built table and every old order-selected value. -/
theorem evaluate_hashGrow_rehash_loop_values_in {F : Type}
    (keyLength table keys stride capacity used values order orderPos oldKeys oldValues oldOrder oldCapacity items : BitVec 64)
    (bits frontier : Nat) (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52) (beforeKeys : frontier ≤ keys.toNat) (beforeValues : frontier ≤ values.toNat)
    (itemsFit : items.toNat < capacity.toNat)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (targets : Set (BitVec 64)) (oldHeaderValues : table.toNat + 72 ≤ oldValues.toNat)
    (oldValuesEnd : oldValues.toNat + oldCapacity.toNat * 8 ≤ frontier) :
    ∀ rank : Nat, ∀ (state : PanSemStateFiniteExact 64 F) (count : BitVec 64),
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state →
      HashGrowOldArrays table oldKeys stride oldValues oldOrder oldCapacity items frontier state →
      HashOrderEntriesBound order capacity count state →
      HashValueEntriesWord used values capacity state →
      HashReverseEntriesBound used orderPos capacity count state →
      HashOrderLinked used order orderPos capacity count state →
      HashTableValuesIn table targets state → HashOrderValuesIn oldOrder oldValues items targets state →
      state.locals.lookup (ofString "t") = some (.val (.word table)) →
      state.locals.lookup (ofString "keys") = some (.val (.word oldKeys)) →
      state.locals.lookup (ofString "stride") = some (.val (.word stride)) →
      state.locals.lookup (ofString "vals") = some (.val (.word oldValues)) →
      state.locals.lookup (ofString "order") = some (.val (.word oldOrder)) →
      state.locals.lookup (ofString "k") = some (.val (.word count)) →
      state.locals.lookup (ofString "nitems") = some (.val (.word items)) →
      count.toNat ≤ items.toNat → items.toNat - count.toNat = rank →
      rank * (capacity.toNat + keyLength.toNat + 4) ≤ state.clock →
      ∃ post, evaluateHOLFiniteState state hashGrowRehashLoop = (none,post) ∧
        HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits post ∧
        HashOrderEntriesBound order capacity items post ∧
        HashValueEntriesWord used values capacity post ∧
        HashReverseEntriesBound used orderPos capacity items post ∧
        HashOrderLinked used order orderPos capacity items post ∧
        HashGrowOldArrays table oldKeys stride oldValues oldOrder oldCapacity items frontier post ∧
        HashTableValuesIn table targets post ∧ HashOrderValuesIn oldOrder oldValues items targets post ∧
        post.locals.lookup (ofString "k") = some (.val (.word items)) ∧
        state.clock ≤ post.clock + rank * (capacity.toNat + keyLength.toNat + 4) ∧ post.clock ≤ state.clock ∧
        post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
        (∀ name, name ≠ ofString "k" → post.locals.lookup name = state.locals.lookup name) ∧
        (∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < frontier →
          post.memory watched = state.memory watched) := by
  classical
  intro rank
  induction rank using Nat.strongRecOn with
  | ind rank ih =>
    intro state count valid old entries valueEntries reverseEntries linked registered oldRegistered t k s v o counter n inside distance budget
    have small : items.toNat ≤ 33806089496 := by
      have bound := old.valueBound
      have fit := old.itemsBound
      omega
    have condition := eval_hashGrow_rehash_condition state count items counter n inside small
    by_cases guard : count.toNat < items.toNat
    · have positive : 0 < rank := by omega
      have oneCost := Nat.mul_le_mul_right (capacity.toNat + keyLength.toNat + 4) (show 1 ≤ rank by omega)
      have nonzero : state.clock ≠ 0 := by omega
      let entry := decClockHOLFinite state
      have entryValid := valid.after_read state entry keyLength table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
      have entryOld := old.preserved state entry table oldKeys stride oldValues oldOrder oldCapacity items frontier rfl
        (by intro watched lower upper; rfl)
      obtain ⟨next,body,nextValid,nextEntries,nextValues,nextReverse,nextLinked,nextOld,bodyCost,bodyRemaining,nextLocals,globals,code,addresses,endian,bodyFrame⟩ :=
        evaluate_hashGrow_rehash_step_supported entry keyLength table keys stride capacity used values order orderPos count oldKeys oldValues oldOrder oldCapacity items
          bits frontier supported entryValid entryOld beforeKeys beforeValues t k s v o counter guard itemsFit
          (by change capacity.toNat + keyLength.toNat + 3 ≤ state.clock - 1; omega)
          (entries.after_memory state entry order capacity count rfl)
          (valueEntries.after_read state entry used values capacity rfl rfl rfl)
          (reverseEntries.after_read state entry used orderPos capacity count rfl rfl rfl)
          (linked.after_read state entry used order orderPos capacity count rfl rfl rfl) keysBeforeValues
      have nextRegistered : HashTableValuesIn table targets next := by
        have preserved := evaluate_hashGrow_rehash_body_values_in entry keyLength table keys stride capacity used values order orderPos count
          oldKeys oldValues oldOrder oldCapacity items bits frontier supported entryValid entryOld beforeKeys beforeValues
          t k s v o counter guard itemsFit (by change capacity.toNat + keyLength.toNat + 3 ≤ state.clock - 1; omega)
          keysBeforeValues targets (registered.after_read rfl rfl rfl) (oldRegistered.after_memory rfl)
        rw [body] at preserved
        exact preserved
      have nextOldRegistered : HashOrderValuesIn oldOrder oldValues items targets next :=
        oldRegistered.preserved state next table oldKeys stride oldValues oldOrder oldCapacity items frontier old targets
          oldHeaderValues oldValuesEnd bodyFrame
      have progress := hashGrow_rehash_rank count items guard small
      have decrease : items.toNat - (count + 1).toNat < rank := by omega
      have recurrence : rank * (capacity.toNat + keyLength.toNat + 4) =
          (items.toNat - (count + 1).toNat) * (capacity.toNat + keyLength.toNat + 4) + (capacity.toNat + keyLength.toNat + 4) := by
        rw [← distance,← progress.2.2,Nat.add_mul,Nat.one_mul]
      have nextOther : ∀ name, name ≠ ofString "k" → next.locals.lookup name = state.locals.lookup name := by
        intro name different
        rw [nextLocals]
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,entry,decClockHOLFinite]
      have nextCounter : next.locals.lookup (ofString "k") = some (.val (.word (count + 1))) := by
        rw [nextLocals]
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have nextBudget : (items.toNat - (count + 1).toNat) * (capacity.toNat + keyLength.toNat + 4) ≤ next.clock := by
        change state.clock - 1 ≤ next.clock + capacity.toNat + keyLength.toNat + 3 at bodyCost
        rw [recurrence] at budget
        omega
      obtain ⟨post,tail,postValid,postEntries,postValues,postReverse,postLinked,postOld,postRegistered,postOldRegistered,postCounter,cost,remaining,lastGlobals,lastCode,lastAddresses,lastEndian,other,frame⟩ :=
        ih _ decrease next (count + 1) nextValid nextOld nextEntries nextValues nextReverse nextLinked nextRegistered nextOldRegistered
          ((nextOther _ (by decide)).trans t) ((nextOther _ (by decide)).trans k)
          ((nextOther _ (by decide)).trans s) ((nextOther _ (by decide)).trans v)
          ((nextOther _ (by decide)).trans o) nextCounter ((nextOther _ (by decide)).trans n)
          progress.2.1 rfl nextBudget
      have run : evaluateHOLFiniteState state hashGrowRehashLoop = evaluateHOLFiniteState next hashGrowRehashLoop := by
        unfold hashGrowRehashLoop
        rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition,if_pos guard]
        have bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) hashGrowRehashBody = (none,next) := body
        have bounded : ¬(decClockHOLFinite state).clock < next.clock := by
          change next.clock ≤ state.clock - 1 at bodyRemaining
          change ¬state.clock - 1 < next.clock
          omega
        simp [nonzero,bodyRun,fixClockHOLFinite,if_neg bounded]
      refine ⟨post,run.trans tail,postValid,postEntries,postValues,postReverse,postLinked,postOld,postRegistered,postOldRegistered,postCounter,?_,?_,lastGlobals.trans globals,lastCode.trans code,
        lastAddresses.trans addresses,lastEndian.trans endian,?_,?_⟩
      · change state.clock - 1 ≤ next.clock + capacity.toNat + keyLength.toNat + 3 at bodyCost
        rw [recurrence]
        omega
      · change next.clock ≤ state.clock - 1 at bodyRemaining
        omega
      · intro name different
        exact (other name different).trans (nextOther name different)
      · intro watched lower upper
        exact (frame watched lower upper).trans (bodyFrame watched lower upper)
    · have same : count = items := BitVec.eq_of_toNat_eq (by omega)
      have run : evaluateHOLFiniteState state hashGrowRehashLoop = (none,state) := by
        unfold hashGrowRehashLoop
        rw [evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition,if_neg guard]
        simp
      subst count
      exact ⟨state,run,valid,entries,valueEntries,reverseEntries,linked,old,registered,oldRegistered,counter,by omega,Nat.le_refl _,rfl,rfl,rfl,rfl,
        by intro name different; rfl,by intro watched lower upper; rfl⟩

#print axioms evaluate_hashGrow_rehash_loop_values_in
end InitECandidate.Runtime
