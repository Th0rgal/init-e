import InitECandidate.Runtime.SourceCostSharpCrepBasis
import InitECandidate.Runtime.SourceCostCrepLeaf
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-! Exact-price executed-work ceilings for straight-line compiler output. -/

/-- A uniform exact-price work ceiling for a non-recursive Crep fragment. -/
def CrepBoundedS (program : CrepProgHOL 64) (bound : Nat) : Prop :=
  ∀ (σ : Type) (t : CrepSemHOLState 64 σ), ∃ w, CrepWorkS t program w ∧ w ≤ bound

theorem CrepBoundedS.mono {program : CrepProgHOL 64} {small large : Nat}
    (bounded : CrepBoundedS program small) (le : small ≤ large) : CrepBoundedS program large := by
  intro σ t
  obtain ⟨w, work, bound⟩ := bounded σ t
  exact ⟨w, work, by omega⟩

theorem sharp_bounded_skip : CrepBoundedS .skip 2 := fun _ t => ⟨2, CrepWorkP.skip t, Nat.le_refl _⟩

theorem sharp_bounded_raise (code : BitVec 64) : CrepBoundedS (.raise code) 3 :=
  fun _ t => ⟨3, CrepWorkP.raise t code, Nat.le_refl _⟩

theorem sharp_bounded_assign (name : Nat) (value : CrepExpHOL 64) :
    CrepBoundedS (.assign name value) (2 + loopNodePrice value) :=
  fun _ t => ⟨_, CrepWorkP.assign t name value, Nat.le_refl _⟩

theorem sharp_bounded_storeGlob (address : BitVec 5) (value : CrepExpHOL 64) :
    CrepBoundedS (.storeGlob address value) (2 + loopNodePrice value) :=
  fun _ t => ⟨_, CrepWorkP.storeGlob t address value, Nat.le_refl _⟩

theorem sharp_bounded_store (address value : CrepExpHOL 64) :
    CrepBoundedS (.store address value) (2 + loopNodePrice address + loopNodePrice value) :=
  fun _ t => ⟨_, CrepWorkP.store t address value, Nat.le_refl _⟩

theorem sharp_bounded_store32 (address value : CrepExpHOL 64) :
    CrepBoundedS (.store32 address value) (2 + loopNodePrice address + loopNodePrice value) :=
  fun _ t => ⟨_, CrepWorkP.store32 t address value, Nat.le_refl _⟩

theorem sharp_bounded_storeByte (address value : CrepExpHOL 64) :
    CrepBoundedS (.storeByte address value) (2 + loopNodePrice address + loopNodePrice value) :=
  fun _ t => ⟨_, CrepWorkP.storeByte t address value, Nat.le_refl _⟩

theorem sharp_bounded_return (values : List (CrepExpHOL 64)) :
    CrepBoundedS (.return values) (2 + sharpCrepList values + values.length) :=
  fun _ t => ⟨_, CrepWorkP.returnStmt t values, Nat.le_refl _⟩

/-- Sequencing is structural and follows the actual successor. -/
theorem sharp_bounded_seq {first second : CrepProgHOL 64} {a b : Nat}
    (one : CrepBoundedS first a) (two : CrepBoundedS second b) :
    CrepBoundedS (.seq first second) (a + b) := by
  intro σ t
  obtain ⟨w1, work1, bound1⟩ := one σ t
  rcases run : evalCrepSemHOLProgExact t first with ⟨_ | result, middle⟩
  · obtain ⟨w2, work2, bound2⟩ := two σ middle
    exact ⟨w1 + w2, CrepWorkP.seqNext work1 run work2, by omega⟩
  · exact ⟨w1, CrepWorkP.seqStop work1 run, by omega⟩

theorem sharpCrepList_head (head : CrepExpHOL 64) (tail : List (CrepExpHOL 64)) :
    loopNodePrice head + 1 ≤ sharpCrepList (head :: tail) := by
  rw [sharpCrepList_cons]; omega

/-- Nested declarations pay each attempted initializer. -/
theorem sharp_bounded_nestedDecs (names : List Nat) (values : List (CrepExpHOL 64))
    {body : CrepProgHOL 64} {b : Nat} (bodyBounded : CrepBoundedS body b) :
    CrepBoundedS (nestedDecsHOL names values body)
      (2 + names.length + sharpCrepList values + b) := by
  intro σ t
  induction names generalizing values t with
  | nil =>
    cases values with
    | nil =>
      obtain ⟨w, work, bound⟩ := bodyBounded σ t
      exact ⟨w, by simpa [nestedDecsHOL] using work, by omega⟩
    | cons value values =>
      exact ⟨2, by simpa [nestedDecsHOL] using CrepWorkP.skip t, by omega⟩
  | cons name names ih =>
    cases values with
    | nil => exact ⟨2, by simpa [nestedDecsHOL] using CrepWorkP.skip t, by omega⟩
    | cons value values =>
      simp only [nestedDecsHOL, List.length_cons, sharpCrepList_cons]
      rcases evaluated : evalCrepSemHOLExp t value with _ | word
      · exact ⟨_, CrepWorkP.decFailure evaluated, by omega⟩
      · obtain ⟨w, work, bound⟩ := ih values { t with locals := t.locals.updateEq (name, word) }
        exact ⟨_, CrepWorkP.dec evaluated work, by omega⟩

theorem sharp_bounded_assign_seq (names : List Nat) (values : List (CrepExpHOL 64)) :
    CrepBoundedS (crepNestedSeqHOL (List.zipWith CrepProgHOL.assign names values))
      (2 + values.length + sharpCrepList values) := by
  induction names generalizing values with
  | nil =>
    simp only [List.zipWith, crepNestedSeqHOL]
    exact sharp_bounded_skip.mono (by omega)
  | cons name names ih =>
    cases values with
    | nil =>
      simp only [List.zipWith, crepNestedSeqHOL]
      exact sharp_bounded_skip.mono (by omega)
    | cons value values =>
      simp only [List.zipWith, crepNestedSeqHOL]
      refine (sharp_bounded_seq (sharp_bounded_assign name value) (ih values)).mono ?_
      simp only [List.length_cons, sharpCrepList_cons]
      omega

theorem sharp_bounded_stores (address : CrepExpHOL 64) (names : List Nat) (offset : BitVec 64) :
    CrepBoundedS (crepNestedSeqHOL (storesHOL address (names.map CrepExpHOL.var) offset))
      (2 + names.length * (8 + loopNodePrice address)) := by
  induction names generalizing offset with
  | nil => simpa [storesHOL, crepNestedSeqHOL] using sharp_bounded_skip
  | cons name names ih =>
    simp only [List.map_cons, storesHOL, crepNestedSeqHOL]
    have destinationWork : loopNodePrice
        (if (offset == 0) = true then address else .op .add [address, .const offset]) ≤
          4 + loopNodePrice address := by
      split <;> simp [loopNodePrice, loopPriceList] <;> omega
    refine (sharp_bounded_seq (sharp_bounded_store _ (.var name)) (ih _)).mono ?_
    simp only [List.length_cons, loopNodePrice, Nat.succ_mul]
    omega

theorem sharp_bounded_storeGlobals (address : BitVec 5) (names : List Nat) :
    CrepBoundedS (crepNestedSeqHOL (storeGlobalsHOL address (names.map CrepExpHOL.var)))
      (2 + 4 * names.length) := by
  induction names generalizing address with
  | nil => simpa [storeGlobalsHOL, crepNestedSeqHOL] using sharp_bounded_skip
  | cons name names ih =>
    simp only [List.map_cons, storeGlobalsHOL, crepNestedSeqHOL]
    refine (sharp_bounded_seq (sharp_bounded_storeGlob address (.var name)) (ih _)).mono ?_
    simp only [List.length_cons, loopNodePrice]
    omega

/-- Local assignment output, both direct and through fresh temporaries. -/
theorem sharp_bounded_local_assign (context : PanToCrepContextExact 64) (name : MlStringHOL)
    (expression : ExpHOL 64) :
    CrepBoundedS (compileLocalAssignExactHOLW context name expression)
      (4 + 5 * (compileExpExactHOLW context expression).1.length +
        sharpCrepList (compileExpExactHOLW context expression).1) := by
  unfold compileLocalAssignExactHOLW
  rcases compileExpExactHOLW context expression with ⟨values, shape⟩
  simp only []
  split
  · exact sharp_bounded_skip.mono (by omega)
  · rename_i _ names _
    split
    · exact sharp_bounded_skip.mono (by omega)
    · split
      · exact (sharp_bounded_assign_seq names values).mono (by omega)
      · have seqBounded := sharp_bounded_assign_seq names
          (((List.range names.length).map (fun index => context.vmax + index + 1)).map
            CrepExpHOL.var)
        rw [sharp_variables] at seqBounded
        have decs := sharp_bounded_nestedDecs
          ((List.range names.length).map (fun index => context.vmax + index + 1)) values
          seqBounded
        refine decs.mono ?_
        rename_i lengths _
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at lengths
        simp only [List.length_map, List.length_range] at seqBounded ⊢
        omega

theorem sharp_bounded_store_compiled (context : PanToCrepContextExact 64) (address value : ExpHOL 64) :
    CrepBoundedS (compileStoreExactHOLW context address value)
      (6 + 11 * (compileExpExactHOLW context value).1.length +
        sharpCrepList (compileExpExactHOLW context address).1 +
        sharpCrepList (compileExpExactHOLW context value).1) := by
  unfold compileStoreExactHOLW
  rcases compileExpExactHOLW context address with ⟨_ | ⟨compiledAddress, rest⟩, addressShape⟩
  · exact sharp_bounded_skip.mono (by omega)
  · rcases compileExpExactHOLW context value with ⟨values, valueShape⟩
    simp only []
    split
    · exact sharp_bounded_skip.mono (by omega)
    · rename_i lengths
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at lengths
      have headWork := sharpCrepList_head compiledAddress rest
      let valueNames := (List.range (sizeOfShapeHOL valueShape)).map
        (fun index => context.vmax + 1 + index + 1)
      have decs := sharp_bounded_nestedDecs ((context.vmax + 1) :: valueNames)
        (compiledAddress :: values) (sharp_bounded_stores (.var (context.vmax + 1)) valueNames 0)
      refine decs.mono ?_
      simp only [valueNames, List.length_cons, List.length_map, List.length_range, sharpCrepList_cons,
        loopNodePrice]
      rw [lengths]
      omega

theorem sharp_bounded_store32_compiled (context : PanToCrepContextExact 64) (address value : ExpHOL 64) :
    CrepBoundedS (compileStore32ExactHOLW context address value)
      (2 + sharpCrepList (compileExpExactHOLW context address).1 +
        sharpCrepList (compileExpExactHOLW context value).1) := by
  unfold compileStore32ExactHOLW
  split
  · rename_i a ta _ v tv _ ha hv
    rw [ha, hv]
    dsimp only
    have := sharpCrepList_head a ta
    have := sharpCrepList_head v tv
    exact (sharp_bounded_store32 a v).mono (by omega)
  · exact sharp_bounded_skip.mono (by omega)

theorem sharp_bounded_storeByte_compiled (context : PanToCrepContextExact 64)
    (address value : ExpHOL 64) :
    CrepBoundedS (compileStoreByteExactHOLW context address value)
      (2 + sharpCrepList (compileExpExactHOLW context address).1 +
        sharpCrepList (compileExpExactHOLW context value).1) := by
  unfold compileStoreByteExactHOLW
  split
  · rename_i a ta _ v tv _ ha hv
    rw [ha, hv]
    dsimp only
    have := sharpCrepList_head a ta
    have := sharpCrepList_head v tv
    exact (sharp_bounded_storeByte a v).mono (by omega)
  · exact sharp_bounded_skip.mono (by omega)

theorem sharp_bounded_return_compiled (context : PanToCrepContextExact 64) (expression : ExpHOL 64) :
    CrepBoundedS (compileReturnExactHOLW context expression)
      (2 + sharpCrepList (compileExpExactHOLW context expression).1 +
        (compileExpExactHOLW context expression).1.length) := by
  unfold compileReturnExactHOLW
  rcases compileExpExactHOLW context expression with ⟨values, shape⟩
  simp only []
  split
  · exact (sharp_bounded_return []).mono (by simp only [sharpCrepList, loopPriceList, List.length_nil]; omega)
  · exact sharp_bounded_return values

theorem sharp_bounded_raise_compiled (context : PanToCrepContextExact 64) (exceptionName : MlStringHOL)
    (expression : ExpHOL 64) :
    CrepBoundedS (compileRaiseExactHOLW context exceptionName expression)
      (7 + 5 * (compileExpExactHOLW context expression).1.length +
        sharpCrepList (compileExpExactHOLW context expression).1) := by
  unfold compileRaiseExactHOLW
  split
  · exact sharp_bounded_skip.mono (by omega)
  · rename_i code _
    rcases compileExpExactHOLW context expression with ⟨values, shape⟩
    simp only []
    split
    · exact sharp_bounded_skip.mono (by omega)
    · rename_i lengths
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at lengths
      let temporaries := (List.range (sizeOfShapeHOL shape)).map
        (fun index => context.vmax + index + 1)
      have decs := sharp_bounded_nestedDecs temporaries values (sharp_bounded_storeGlobals 0 temporaries)
      refine (sharp_bounded_seq decs (sharp_bounded_raise code)).mono ?_
      simp only [temporaries, List.length_map, List.length_range]
      rw [lengths]
      omega

#print axioms sharp_bounded_nestedDecs
#print axioms sharp_bounded_local_assign
#print axioms sharp_bounded_store_compiled
#print axioms sharp_bounded_raise_compiled
end InitECandidate.Runtime.FineCost
