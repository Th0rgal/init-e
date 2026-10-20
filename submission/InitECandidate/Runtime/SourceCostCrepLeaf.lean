import InitECandidate.Runtime.SourceCostCrepBasis
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-- A uniform executed-work ceiling for a non-recursive Crep fragment: from every
start state, its actual execution (including early failure) has work at most
`bound`. Only straight-line compiler output is proved to satisfy this. -/
def CrepBounded (program : CrepProgHOL 64) (bound : Nat) : Prop :=
  ∀ (σ : Type) (t : CrepSemHOLState 64 σ), ∃ w, CrepWork t program w ∧ w ≤ bound

theorem CrepBounded.mono {program : CrepProgHOL 64} {small large : Nat}
    (bounded : CrepBounded program small) (le : small ≤ large) : CrepBounded program large := by
  intro σ t
  obtain ⟨w, work, bound⟩ := bounded σ t
  exact ⟨w, work, by omega⟩

theorem bounded_skip : CrepBounded .skip 1 := fun _ t => ⟨1, CrepWork.skip t, Nat.le_refl _⟩

theorem bounded_raise (code : BitVec 64) : CrepBounded (.raise code) 1 :=
  fun _ t => ⟨1, CrepWork.raise t code, Nat.le_refl _⟩

theorem bounded_assign (name : Nat) (value : CrepExpHOL 64) :
    CrepBounded (.assign name value) (1 + crepNodeWork value) :=
  fun _ t => ⟨_, CrepWork.assign t name value, Nat.le_refl _⟩

theorem bounded_storeGlob (address : BitVec 5) (value : CrepExpHOL 64) :
    CrepBounded (.storeGlob address value) (1 + crepNodeWork value) :=
  fun _ t => ⟨_, CrepWork.storeGlob t address value, Nat.le_refl _⟩

theorem bounded_store (address value : CrepExpHOL 64) :
    CrepBounded (.store address value) (1 + crepNodeWork address + crepNodeWork value) :=
  fun _ t => ⟨_, CrepWork.store t address value, Nat.le_refl _⟩

theorem bounded_store32 (address value : CrepExpHOL 64) :
    CrepBounded (.store32 address value) (1 + crepNodeWork address + crepNodeWork value) :=
  fun _ t => ⟨_, CrepWork.store32 t address value, Nat.le_refl _⟩

theorem bounded_storeByte (address value : CrepExpHOL 64) :
    CrepBounded (.storeByte address value) (1 + crepNodeWork address + crepNodeWork value) :=
  fun _ t => ⟨_, CrepWork.storeByte t address value, Nat.le_refl _⟩

theorem bounded_return (values : List (CrepExpHOL 64)) :
    CrepBounded (.return values) (1 + crepListWork values + values.length) :=
  fun _ t => ⟨_, CrepWork.returnStmt t values, Nat.le_refl _⟩

/-- Sequencing follows the actual successor: a stopped first statement skips
the second statement's work. -/
theorem bounded_seq {first second : CrepProgHOL 64} {a b : Nat}
    (one : CrepBounded first a) (two : CrepBounded second b) :
    CrepBounded (.seq first second) (1 + a + b) := by
  intro σ t
  obtain ⟨w1, work1, bound1⟩ := one σ t
  rcases run : evalCrepSemHOLProgExact t first with ⟨_ | result, middle⟩
  · obtain ⟨w2, work2, bound2⟩ := two σ middle
    exact ⟨1 + w1 + w2, CrepWork.seqNext work1 run work2, by omega⟩
  · exact ⟨1 + w1, CrepWork.seqStop work1 run, by omega⟩

/-- Nested declarations pay each attempted initializer; a failed initializer
stops before the body. Mismatched lists compile to `Skip`. -/
theorem bounded_nestedDecs (names : List Nat) (values : List (CrepExpHOL 64))
    {body : CrepProgHOL 64} {b : Nat} (bodyBounded : CrepBounded body b) :
    CrepBounded (nestedDecsHOL names values body)
      (1 + names.length + crepListWork values + b) := by
  intro σ t
  induction names generalizing values t with
  | nil =>
    cases values with
    | nil =>
      obtain ⟨w, work, bound⟩ := bodyBounded σ t
      exact ⟨w, by simpa [nestedDecsHOL] using work, by omega⟩
    | cons value values =>
      exact ⟨1, by simpa [nestedDecsHOL] using CrepWork.skip t, by omega⟩
  | cons name names ih =>
    cases values with
    | nil => exact ⟨1, by simpa [nestedDecsHOL] using CrepWork.skip t, by omega⟩
    | cons value values =>
      simp only [nestedDecsHOL, List.length_cons, crepListWork]
      rcases evaluated : evalCrepSemHOLExp t value with _ | word
      · exact ⟨_, CrepWork.decFailure evaluated, by omega⟩
      · obtain ⟨w, work, bound⟩ := ih values { t with locals := t.locals.updateEq (name, word) }
        exact ⟨_, CrepWork.dec evaluated work, by omega⟩

theorem crepNodeWork_le_list_head (head : CrepExpHOL 64) (tail : List (CrepExpHOL 64)) :
    crepNodeWork head ≤ crepListWork (head :: tail) := by
  simp only [crepListWork]; omega

theorem bounded_assign_seq (names : List Nat) (values : List (CrepExpHOL 64)) :
    CrepBounded (crepNestedSeqHOL (List.zipWith CrepProgHOL.assign names values))
      (1 + 2 * values.length + crepListWork values) := by
  induction names generalizing values with
  | nil =>
    simp only [List.zipWith, crepNestedSeqHOL]
    exact bounded_skip.mono (by omega)
  | cons name names ih =>
    cases values with
    | nil =>
      simp only [List.zipWith, crepNestedSeqHOL]
      exact bounded_skip.mono (by omega)
    | cons value values =>
      simp only [List.zipWith, crepNestedSeqHOL]
      refine (bounded_seq (bounded_assign name value) (ih values)).mono ?_
      simp only [List.length_cons, crepListWork]
      omega

theorem crepListWork_vars (names : List Nat) :
    crepListWork (names.map (CrepExpHOL.var (width := 64))) = names.length := by
  induction names with
  | nil => simp [crepListWork]
  | cons head tail ih => simp [crepListWork, crepNodeWork, ih, Nat.add_comm]

theorem bounded_stores (address : CrepExpHOL 64) (names : List Nat) (offset : BitVec 64) :
    CrepBounded (crepNestedSeqHOL (storesHOL address (names.map CrepExpHOL.var) offset))
      (1 + names.length * (5 + crepNodeWork address)) := by
  induction names generalizing offset with
  | nil => simpa [storesHOL, crepNestedSeqHOL] using bounded_skip
  | cons name names ih =>
    simp only [List.map_cons, storesHOL, crepNestedSeqHOL]
    have destinationWork : crepNodeWork
        (if (offset == 0) = true then address else .op .add [address, .const offset]) ≤
          2 + crepNodeWork address := by
      split <;> simp [crepNodeWork, crepListWork] <;> omega
    refine (bounded_seq (bounded_store _ (.var name)) (ih _)).mono ?_
    simp only [List.length_cons, crepNodeWork, Nat.succ_mul]
    omega

theorem bounded_storeGlobals (address : BitVec 5) (names : List Nat) :
    CrepBounded (crepNestedSeqHOL (storeGlobalsHOL address (names.map CrepExpHOL.var)))
      (1 + 3 * names.length) := by
  induction names generalizing address with
  | nil => simpa [storeGlobalsHOL, crepNestedSeqHOL] using bounded_skip
  | cons name names ih =>
    simp only [List.map_cons, storeGlobalsHOL, crepNestedSeqHOL]
    refine (bounded_seq (bounded_storeGlob address (.var name)) (ih _)).mono ?_
    simp only [List.length_cons, crepNodeWork]
    omega

/-- Local assignment output, both direct and through fresh temporaries. -/
theorem bounded_local_assign (context : PanToCrepContextExact 64) (name : MlStringHOL)
    (expression : ExpHOL 64) :
    CrepBounded (compileLocalAssignExactHOLW context name expression)
      (3 + 4 * (compileExpExactHOLW context expression).1.length +
        crepListWork (compileExpExactHOLW context expression).1) := by
  unfold compileLocalAssignExactHOLW
  rcases compileExpExactHOLW context expression with ⟨values, shape⟩
  simp only []
  split
  · exact bounded_skip.mono (by omega)
  · rename_i _ names _
    split
    · exact bounded_skip.mono (by omega)
    · split
      · exact (bounded_assign_seq names values).mono (by omega)
      · have seqBounded := bounded_assign_seq names
          (((List.range names.length).map (fun index => context.vmax + index + 1)).map
            CrepExpHOL.var)
        rw [crepListWork_vars] at seqBounded
        have decs := bounded_nestedDecs
          ((List.range names.length).map (fun index => context.vmax + index + 1)) values
          seqBounded
        refine decs.mono ?_
        rename_i lengths _
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at lengths
        simp only [List.length_map, List.length_range] at seqBounded ⊢
        omega

theorem bounded_store_compiled (context : PanToCrepContextExact 64) (address value : ExpHOL 64) :
    CrepBounded (compileStoreExactHOLW context address value)
      (4 + 7 * (compileExpExactHOLW context value).1.length +
        crepListWork (compileExpExactHOLW context address).1 +
        crepListWork (compileExpExactHOLW context value).1) := by
  unfold compileStoreExactHOLW
  rcases compileExpExactHOLW context address with ⟨_ | ⟨compiledAddress, rest⟩, addressShape⟩
  · exact bounded_skip.mono (by omega)
  · rcases compileExpExactHOLW context value with ⟨values, valueShape⟩
    simp only []
    split
    · exact bounded_skip.mono (by omega)
    · rename_i lengths
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at lengths
      have headWork := crepNodeWork_le_list_head compiledAddress rest
      let valueNames := (List.range (sizeOfShapeHOL valueShape)).map
        (fun index => context.vmax + 1 + index + 1)
      have decs := bounded_nestedDecs ((context.vmax + 1) :: valueNames)
        (compiledAddress :: values) (bounded_stores (.var (context.vmax + 1)) valueNames 0)
      refine decs.mono ?_
      simp only [valueNames, List.length_cons, List.length_map, List.length_range, crepListWork,
        crepNodeWork]
      rw [lengths]
      have hl : crepListWork (compiledAddress :: rest) =
          crepNodeWork compiledAddress + crepListWork rest := by simp [crepListWork]
      omega

theorem bounded_store32_compiled (context : PanToCrepContextExact 64) (address value : ExpHOL 64) :
    CrepBounded (compileStore32ExactHOLW context address value)
      (1 + crepListWork (compileExpExactHOLW context address).1 +
        crepListWork (compileExpExactHOLW context value).1) := by
  unfold compileStore32ExactHOLW
  split
  · rename_i a ta _ v tv _ ha hv
    rw [ha, hv]
    dsimp only
    have := crepNodeWork_le_list_head a ta
    have := crepNodeWork_le_list_head v tv
    exact (bounded_store32 a v).mono (by omega)
  · exact bounded_skip.mono (by omega)

theorem bounded_storeByte_compiled (context : PanToCrepContextExact 64)
    (address value : ExpHOL 64) :
    CrepBounded (compileStoreByteExactHOLW context address value)
      (1 + crepListWork (compileExpExactHOLW context address).1 +
        crepListWork (compileExpExactHOLW context value).1) := by
  unfold compileStoreByteExactHOLW
  split
  · rename_i a ta _ v tv _ ha hv
    rw [ha, hv]
    dsimp only
    have := crepNodeWork_le_list_head a ta
    have := crepNodeWork_le_list_head v tv
    exact (bounded_storeByte a v).mono (by omega)
  · exact bounded_skip.mono (by omega)

theorem bounded_return_compiled (context : PanToCrepContextExact 64) (expression : ExpHOL 64) :
    CrepBounded (compileReturnExactHOLW context expression)
      (1 + crepListWork (compileExpExactHOLW context expression).1 +
        (compileExpExactHOLW context expression).1.length) := by
  unfold compileReturnExactHOLW
  rcases compileExpExactHOLW context expression with ⟨values, shape⟩
  simp only []
  split
  · exact (bounded_return []).mono (by simp only [crepListWork, List.length_nil]; omega)
  · exact bounded_return values

theorem bounded_raise_compiled (context : PanToCrepContextExact 64) (exceptionName : MlStringHOL)
    (expression : ExpHOL 64) :
    CrepBounded (compileRaiseExactHOLW context exceptionName expression)
      (5 + 4 * (compileExpExactHOLW context expression).1.length +
        crepListWork (compileExpExactHOLW context expression).1) := by
  unfold compileRaiseExactHOLW
  split
  · exact bounded_skip.mono (by omega)
  · rename_i code _
    rcases compileExpExactHOLW context expression with ⟨values, shape⟩
    simp only []
    split
    · exact bounded_skip.mono (by omega)
    · rename_i lengths
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at lengths
      let temporaries := (List.range (sizeOfShapeHOL shape)).map
        (fun index => context.vmax + index + 1)
      have decs := bounded_nestedDecs temporaries values (bounded_storeGlobals 0 temporaries)
      refine (bounded_seq decs (bounded_raise code)).mono ?_
      simp only [temporaries, List.length_map, List.length_range]
      rw [lengths]
      omega

#print axioms bounded_nestedDecs
#print axioms bounded_local_assign
#print axioms bounded_store_compiled
#print axioms bounded_store32_compiled
#print axioms bounded_storeByte_compiled
#print axioms bounded_return_compiled
#print axioms bounded_raise_compiled
end InitECandidate.Runtime.FineCost
