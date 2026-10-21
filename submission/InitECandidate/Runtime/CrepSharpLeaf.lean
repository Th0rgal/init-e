import InitECandidate.Runtime.CrepSharpModel
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-! Model-priced executed-work ceilings for straight-line compiler output. -/

namespace SharpModel
variable (M : SharpModel)

theorem bounded_skip : CrepBoundedM M .skip 0 := fun _ fn t => ⟨0, CrepWorkF.skip fn t, Nat.le_refl _⟩

theorem bounded_raise (code : BitVec 64) : CrepBoundedM M (.raise code) M.S.raise :=
  fun _ fn t => ⟨_, CrepWorkF.raise fn t code, Nat.le_refl _⟩

theorem bounded_assign (name : Nat) (value : CrepExpHOL 64) :
    CrepBoundedM M (.assign name value) (M.pr value) :=
  fun _ fn t => ⟨_, CrepWorkF.assign fn t name value, Nat.le_refl _⟩

theorem bounded_storeGlob (address : BitVec 5) (value : CrepExpHOL 64) :
    CrepBoundedM M (.storeGlob address value) (M.S.storeGlob + M.pr value) :=
  fun _ fn t => ⟨_, CrepWorkF.storeGlob fn t address value, Nat.le_refl _⟩

theorem bounded_store (address value : CrepExpHOL 64) :
    CrepBoundedM M (.store address value) (M.S.store + M.pr address + M.pr value) :=
  fun _ fn t => ⟨_, CrepWorkF.store fn t address value, Nat.le_refl _⟩

theorem bounded_store32 (address value : CrepExpHOL 64) :
    CrepBoundedM M (.store32 address value) (M.S.store32 + M.pr address + M.pr value) :=
  fun _ fn t => ⟨_, CrepWorkF.store32 fn t address value, Nat.le_refl _⟩

theorem bounded_storeByte (address value : CrepExpHOL 64) :
    CrepBoundedM M (.storeByte address value) (M.S.store32 + M.pr address + M.pr value) :=
  fun _ fn t => ⟨_, CrepWorkF.storeByte fn t address value, Nat.le_refl _⟩

theorem bounded_return (values : List (CrepExpHOL 64)) :
    CrepBoundedM M (.return values) (M.S.ret values.length + M.prs values) :=
  fun _ fn t => ⟨_, CrepWorkF.returnStmt fn t values, Nat.le_refl _⟩

/-- Sequencing is structural and follows the actual successor. -/
theorem bounded_seq {first second : CrepProgHOL 64} {a b : Nat}
    (one : CrepBoundedM M first a) (two : CrepBoundedM M second b) :
    CrepBoundedM M (.seq first second) (a + b) := by
  intro σ fn t
  obtain ⟨w1, work1, bound1⟩ := one σ fn t
  rcases run : evalCrepSemHOLProgExact t first with ⟨_ | result, middle⟩
  · obtain ⟨w2, work2, bound2⟩ := two σ fn middle
    exact ⟨w1 + w2, CrepWorkF.seqNext work1 run work2, by omega⟩
  · exact ⟨w1, CrepWorkF.seqStop work1 run, by omega⟩

/-- Nested declarations pay each attempted initializer. -/
theorem bounded_nestedDecs (names : List Nat) (values : List (CrepExpHOL 64))
    {body : CrepProgHOL 64} {b : Nat} (bodyBounded : CrepBoundedM M body b) :
    CrepBoundedM M (nestedDecsHOL names values body) (M.prs values + b) := by
  intro σ fn t
  induction names generalizing values t with
  | nil =>
    cases values with
    | nil =>
      obtain ⟨w, work, bound⟩ := bodyBounded σ fn t
      exact ⟨w, by simpa [nestedDecsHOL] using work, by simp only [prs_nil]; omega⟩
    | cons value values =>
      have hs : CrepWorkM M fn t .skip 0 := CrepWorkF.skip fn t
      exact ⟨0, by simpa [nestedDecsHOL] using hs, by omega⟩
  | cons name names ih =>
    cases values with
    | nil =>
      have hs : CrepWorkM M fn t .skip 0 := CrepWorkF.skip fn t
      exact ⟨0, by simpa [nestedDecsHOL] using hs, by omega⟩
    | cons value values =>
      simp only [nestedDecsHOL, prs_cons]
      rcases evaluated : evalCrepSemHOLExp t value with _ | word
      · exact ⟨_, CrepWorkF.decFailure evaluated, by omega⟩
      · obtain ⟨w, work, bound⟩ := ih values { t with locals := t.locals.updateEq (name, word) }
        exact ⟨_, CrepWorkF.dec evaluated work, by omega⟩

theorem bounded_assign_seq (names : List Nat) (values : List (CrepExpHOL 64)) :
    CrepBoundedM M (crepNestedSeqHOL (List.zipWith CrepProgHOL.assign names values))
      (M.prs values) := by
  induction names generalizing values with
  | nil =>
    simp only [List.zipWith, crepNestedSeqHOL]
    exact M.bounded_mono M.bounded_skip (by omega)
  | cons name names ih =>
    cases values with
    | nil =>
      simp only [List.zipWith, crepNestedSeqHOL]
      exact M.bounded_mono M.bounded_skip (by omega)
    | cons value values =>
      simp only [List.zipWith, crepNestedSeqHOL]
      refine M.bounded_mono (M.bounded_seq (M.bounded_assign name value) (ih values)) ?_
      simp only [prs_cons]
      omega

/-- Per-word store price from an address of price `a`. -/
abbrev storeWord (a : Nat) : Nat := M.S.store + a + M.O + M.V

theorem bounded_stores (x : Nat) (names : List Nat) (offset : BitVec 64) :
    CrepBoundedM M (crepNestedSeqHOL (storesHOL (.var x) (names.map CrepExpHOL.var) offset))
      (names.length * M.storeWord M.V) := by
  induction names generalizing offset with
  | nil => simpa [storesHOL, crepNestedSeqHOL] using M.bounded_skip
  | cons name names ih =>
    simp only [List.map_cons, storesHOL, crepNestedSeqHOL]
    have destinationWork : M.pr
        (if (offset == 0) = true then .var x else .op .add [.var x, .const offset]) ≤ M.V + M.O := by
      have := M.varOk x; have := M.offOk x offset
      split <;> omega
    have hv := M.varOk name
    refine M.bounded_mono (M.bounded_seq (M.bounded_store _ (.var name)) (ih _)) ?_
    simp only [List.length_cons, Nat.succ_mul, storeWord]
    omega

theorem storeWordsCost_succ (S : StmtK) (V O a n : Nat) :
    storeWordsCost S V O a (n + 1) = n * (S.store + a + O + V) + (S.store + a + V) := by
  unfold storeWordsCost
  have h1 : n + 1 - (n + 1 - 1) = 1 := by omega
  rw [h1, Nat.mul_one, Nat.succ_mul]
  omega

/-- Stores from offset zero: the first word stores at the address itself. -/
theorem bounded_stores_zero (x : Nat) (names : List Nat) :
    CrepBoundedM M (crepNestedSeqHOL (storesHOL (.var x) (names.map CrepExpHOL.var) 0))
      (storeWordsCost M.S M.V M.O M.V names.length) := by
  cases names with
  | nil => simpa [storesHOL, crepNestedSeqHOL, storeWordsCost] using M.bounded_skip
  | cons name names =>
    simp only [List.map_cons, storesHOL, crepNestedSeqHOL]
    have hv := M.varOk name
    have hx := M.varOk x
    have hif : M.pr (if ((0 : BitVec 64) == 0) = true then .var x
        else .op .add [.var x, .const 0]) = M.pr (.var x) := by simp
    refine M.bounded_mono (M.bounded_seq (M.bounded_store _ (.var name)) (M.bounded_stores x names _)) ?_
    rw [List.length_cons, storeWordsCost_succ]
    simp only [storeWord]
    omega

theorem bounded_storeGlobals (address : BitVec 5) (names : List Nat) :
    CrepBoundedM M (crepNestedSeqHOL (storeGlobalsHOL address (names.map CrepExpHOL.var)))
      (names.length * (M.S.storeGlob + M.V)) := by
  induction names generalizing address with
  | nil => simpa [storeGlobalsHOL, crepNestedSeqHOL] using M.bounded_skip
  | cons name names ih =>
    simp only [List.map_cons, storeGlobalsHOL, crepNestedSeqHOL]
    refine M.bounded_mono (M.bounded_seq (M.bounded_storeGlob address (.var name)) (ih _)) ?_
    have := M.varOk name
    simp only [List.length_cons, Nat.succ_mul]
    omega

/-- Local assignment output, both direct and through fresh temporaries. -/
theorem bounded_local_assign (context : PanToCrepContextExact 64) (name : MlStringHOL)
    (expression : ExpHOL 64) :
    CrepBoundedM M (compileLocalAssignExactHOLW context name expression)
      ((compileExpExactHOLW context expression).1.length * M.V +
        M.prs (compileExpExactHOLW context expression).1) := by
  unfold compileLocalAssignExactHOLW
  rcases compileExpExactHOLW context expression with ⟨values, shape⟩
  simp only []
  split
  · exact M.bounded_mono M.bounded_skip (by omega)
  · rename_i _ names _
    split
    · exact M.bounded_mono M.bounded_skip (by omega)
    · split
      · exact M.bounded_mono (M.bounded_assign_seq names values) (by omega)
      · have seqBounded := M.bounded_assign_seq names
          (((List.range names.length).map (fun index => context.vmax + index + 1)).map CrepExpHOL.var)
        have vars := M.prs_variables ((List.range names.length).map (fun index => context.vmax + index + 1))
        have decs := M.bounded_nestedDecs
          ((List.range names.length).map (fun index => context.vmax + index + 1)) values seqBounded
        refine M.bounded_mono decs ?_
        rename_i lengths _
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at lengths
        simp only [List.length_map, List.length_range] at seqBounded vars ⊢
        try rw [lengths] at vars
        rw [lengths]
        omega

theorem bounded_store_compiled (context : PanToCrepContextExact 64) (address value : ExpHOL 64) :
    CrepBoundedM M (compileStoreExactHOLW context address value)
      (storeWordsCost M.S M.V M.O M.V (compileExpExactHOLW context value).1.length +
        M.prs (compileExpExactHOLW context address).1 +
        M.prs (compileExpExactHOLW context value).1) := by
  unfold compileStoreExactHOLW
  rcases compileExpExactHOLW context address with ⟨_ | ⟨compiledAddress, rest⟩, addressShape⟩
  · exact M.bounded_mono M.bounded_skip (by omega)
  · rcases compileExpExactHOLW context value with ⟨values, valueShape⟩
    simp only []
    split
    · exact M.bounded_mono M.bounded_skip (by omega)
    · rename_i lengths
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at lengths
      have headWork := M.prs_head compiledAddress rest
      let valueNames := (List.range (sizeOfShapeHOL valueShape)).map
        (fun index => context.vmax + 1 + index + 1)
      have decs := M.bounded_nestedDecs ((context.vmax + 1) :: valueNames)
        (compiledAddress :: values) (M.bounded_stores_zero (context.vmax + 1) valueNames)
      refine M.bounded_mono decs ?_
      simp only [valueNames, List.length_map, List.length_range, prs_cons]
      rw [lengths]
      omega

theorem bounded_store32_compiled (context : PanToCrepContextExact 64) (address value : ExpHOL 64) :
    CrepBoundedM M (compileStore32ExactHOLW context address value)
      (M.S.store32 + M.prs (compileExpExactHOLW context address).1 +
        M.prs (compileExpExactHOLW context value).1) := by
  unfold compileStore32ExactHOLW
  split
  · rename_i a ta _ v tv _ ha hv
    rw [ha, hv]
    dsimp only
    have := M.prs_head a ta
    have := M.prs_head v tv
    exact M.bounded_mono (M.bounded_store32 a v) (by omega)
  · exact M.bounded_mono M.bounded_skip (by omega)

theorem bounded_storeByte_compiled (context : PanToCrepContextExact 64) (address value : ExpHOL 64) :
    CrepBoundedM M (compileStoreByteExactHOLW context address value)
      (M.S.store32 + M.prs (compileExpExactHOLW context address).1 +
        M.prs (compileExpExactHOLW context value).1) := by
  unfold compileStoreByteExactHOLW
  split
  · rename_i a ta _ v tv _ ha hv
    rw [ha, hv]
    dsimp only
    have := M.prs_head a ta
    have := M.prs_head v tv
    exact M.bounded_mono (M.bounded_storeByte a v) (by omega)
  · exact M.bounded_mono M.bounded_skip (by omega)

theorem bounded_return_compiled (context : PanToCrepContextExact 64) (expression : ExpHOL 64) :
    CrepBoundedM M (compileReturnExactHOLW context expression)
      (max (M.S.ret 0) (M.S.ret (compileExpExactHOLW context expression).1.length) +
        M.prs (compileExpExactHOLW context expression).1) := by
  unfold compileReturnExactHOLW
  rcases compileExpExactHOLW context expression with ⟨values, shape⟩
  simp only []
  split
  · exact M.bounded_mono (M.bounded_return []) (by simp only [List.length_nil, prs_nil]; omega)
  · exact M.bounded_mono (M.bounded_return values) (by omega)

theorem bounded_raise_compiled (context : PanToCrepContextExact 64) (exceptionName : MlStringHOL)
    (expression : ExpHOL 64) :
    CrepBoundedM M (compileRaiseExactHOLW context exceptionName expression)
      (M.S.raise + (compileExpExactHOLW context expression).1.length * (M.S.storeGlob + M.V) +
        M.prs (compileExpExactHOLW context expression).1) := by
  unfold compileRaiseExactHOLW
  split
  · exact M.bounded_mono M.bounded_skip (by omega)
  · rename_i code _
    rcases compileExpExactHOLW context expression with ⟨values, shape⟩
    simp only []
    split
    · exact M.bounded_mono M.bounded_skip (by omega)
    · rename_i lengths
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at lengths
      let temporaries := (List.range (sizeOfShapeHOL shape)).map (fun index => context.vmax + index + 1)
      have decs := M.bounded_nestedDecs temporaries values (M.bounded_storeGlobals 0 temporaries)
      refine M.bounded_mono (M.bounded_seq decs (M.bounded_raise code)) ?_
      simp only [temporaries, List.length_map, List.length_range]
      rw [lengths]
      omega

end SharpModel

#print axioms SharpModel.bounded_nestedDecs
#print axioms SharpModel.bounded_local_assign
#print axioms SharpModel.bounded_store_compiled
#print axioms SharpModel.bounded_raise_compiled
end InitECandidate.Runtime.FineCost
