import InitECandidate.Runtime.TransactionStorageOuterRegisteredValuesIn
import InitECandidate.Runtime.TrapNoReturn
import InitECandidate.Runtime.TrapNoTimeout
import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stateStorageAccountGuard : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.var .local (ofString "a")) (.const 1))
    (.raise (ofString "StateErr") (.const 3)) .skip) stateStorageOuterScope

theorem source_setStorage_account_guard :
    stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_set_storage) = stateStorageAccountGuard := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original missing-account guard either exits without returning or enters
the bounded storage continuation; both cases are covered by the same bound. -/
theorem TransactionRegistryWorld.storage_guard_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count outer addr key a b c d account : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables) (targetsSubset : targets ⊆ tables)
    (typed : ∀ inner ∈ targets, widths inner = 32 ∧ inner ∉ watched)
    (outerWatched : outer ∈ watched)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (accountLocal : state.locals.lookup (ofString "a") = some (.val (.word account)))
    (binding : (32,outer) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables)
    (addrLocal : state.locals.lookup (ofString "addr") = some (.val (.word addr)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (addrAligned : addr.toNat % 8 = 0) (keyAligned : key.toNat % 8 = 0)
    (addrWords : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (addr + BitVec.ofNat 64 offset))
    (addrBytes : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (panByteAlignHOL (addr + BitVec.ofNat 64 offset)))
    (keyWords : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 77 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageAccountGuard = (result,post) ∧
      state.clock ≤ post.clock + 2 ^ 77 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ nextWidths nextTables nextTargets nextCount,
        TransactionRegistryWorld nextWidths nextTables fieldPointer ts journal snapshot nextCount post ∧
        watched ⊆ nextTables ∧ nextTargets ⊆ nextTables ∧
        (∀ inner ∈ nextTargets, nextWidths inner = 32 ∧ inner ∉ watched) ∧
        (∀ other ∈ watched, HashTableValuesIn other nextTargets post) ∧
        JournalSavedValuesIn journal nextCount.toNat watched nextTargets post) := by
  classical
  by_cases rejected : account = 1
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "a")) (.const 1)) = some (.val (.word (1 : BitVec 64))) := by
      simp [evalHOLExact,accountLocal,Compiler.Encoders.Asm.wordCmpHOL,rejected]
    let raise : ProgHOL 64 := .raise (ofString "StateErr") (.const 3)
    have nonempty : (evaluateHOLFiniteState state raise).1 ≠ none := by
      rw [evaluateHOLFiniteState_raise]
      split
      · dsimp only
        split <;> simp
      · simp
    have full : evaluateHOLFiniteState state stateStorageAccountGuard = evaluateHOLFiniteState state raise := by
      unfold stateStorageAccountGuard
      rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
      change (let output := evaluateHOLFiniteState state raise; _) = _
      cases output : evaluateHOLFiniteState state raise with
      | mk result post =>
        have nonemptyResult : result ≠ none := by simpa only [output] using nonempty
        cases result with
        | none => exact False.elim (nonemptyResult rfl)
        | some result => rfl
    have clock := clockPreserving_raise (σ := F) (ofString "StateErr") (.const (3 : BitVec 64)) state
    rw [full]
    refine ⟨_,_,rfl,?_,?_,evaluate_raise_no_timeout state _ _,?_⟩
    · change state.clock ≤ (evaluateHOLFiniteState state raise).2.clock + 2 ^ 77
      change (evaluateHOLFiniteState state raise).2.clock = state.clock at clock
      omega
    · exact Nat.le_of_eq clock
    · intro value success
      exact False.elim (evaluate_raise_no_return state _ _ value success)
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "a")) (.const 1)) = some (.val (.word (0 : BitVec 64))) := by
      simp [evalHOLExact,accountLocal,Compiler.Encoders.Asm.wordCmpHOL]
      exact rejected
    have full : evaluateHOLFiniteState state stateStorageAccountGuard = evaluateHOLFiniteState state stateStorageOuterScope := by
      unfold stateStorageAccountGuard
      rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
      simp [evaluateHOLFiniteState_skip]
    rw [full]
    exact valid.storage_outer_registered_values_in state widths tables fieldPointer ts journal snapshot count outer addr key a b c d
      watched targets watchedSubset targetsSubset typed outerWatched registered saved binding addrLocal keyLocal valueLocal
      addrAligned keyAligned addrWords addrBytes keyWords keyBytes ticks

#print axioms source_setStorage_account_guard
#print axioms TransactionRegistryWorld.storage_guard_registered_values_in
end InitECandidate.Runtime
