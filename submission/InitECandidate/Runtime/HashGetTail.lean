import InitECandidate.Runtime.HashHasTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashGetTail : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.var .local (ofString "i")) (.load .one (hashLocalAddress (ofString "t") 16)))
      (.return (.rstruct [.const 0,.const 0])) .skip)
    (.return (.rstruct [.const 1,.load .one (.op .add [.load .one (hashLocalAddress (ofString "t") 40),
      .panop .mul [.var .local (ofString "i"),.const 8]])]))

theorem source_hashGet_body : sourceFunctionBody Guest.guestFn_htab_get =
    .decCall (ofString "i") .one (ofString "htab_find_slot")
      [.var .local (ofString "t"),.var .local (ofString "key")] hashGetTail := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Actual get-table tail returns its presence/value tuple at zero source
clocks, loading a value only when lookup returned an in-range slot. -/
theorem evaluate_hashGetTail {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table index capacity values : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (inside : index.toNat ≤ capacity.toNat)
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain40 : state.memaddrs (table + 40)) (cell40 : state.memory (table + 40) = .word values)
    (valueDomain : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → state.memaddrs (values + slot * 8)) :
    ∃ present value : BitVec 64, (present = 0 ∨ present = 1) ∧ evaluateHOLFiniteState state hashGetTail =
      (some (.returned (.rStruct [.val (.word present),.val (.word value)])),emptyLocalsHOLFinite state) := by
  have d16 : state.memaddrs (table + 16#64) := domain16
  have c16 : state.memory (table + 16#64) = .word capacity := cell16
  have d40 : state.memaddrs (table + 40#64) := domain40
  have c40 : state.memory (table + 40#64) = .word values := cell40
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "i")) (.load .one (hashLocalAddress (ofString "t") 16))) =
      some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .equal index capacity then 1 else 0))) := by
    simp [evalHOLExact,evalListHOLExact,hashLocalAddress,tableLocal,indexLocal,wordOpHOL,wordOp,
      valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,d16,c16]
  cases flag : Compiler.Encoders.Asm.wordCmpHOL .equal index capacity with
  | true =>
    refine ⟨0,0,Or.inl rfl,?_⟩
    unfold hashGetTail
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    simp only [flag]
    simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,shapeOfHOLExact]
  | false =>
    have different : index ≠ capacity := by
      intro same
      rw [same] at flag
      simp [Compiler.Encoders.Asm.wordCmpHOL] at flag
    have strict : index.toNat < capacity.toNat := by
      have ne : index.toNat ≠ capacity.toNat := fun same => different (BitVec.eq_of_toNat_eq same)
      omega
    obtain ⟨value,cell⟩ : ∃ value : BitVec 64, state.memory (values + index * 8) = .word value := by
      cases state.memory (values + index * 8) with | word value => exact ⟨value,rfl⟩
    have vd : state.memaddrs (values + index * 8#64) := valueDomain index strict
    have vc : state.memory (values + index * 8#64) = .word value := cell
    have returned : evaluateHOLFiniteState state
        (.return (.rstruct [.const 1,.load .one (.op .add [.load .one (hashLocalAddress (ofString "t") 40),
          .panop .mul [.var .local (ofString "i"),.const 8]])])) =
        (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word value)])),emptyLocalsHOLFinite state) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,hashLocalAddress,tableLocal,indexLocal,
        wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,d40,c40,vd,vc,shapeOfHOLExact]
    refine ⟨1,value,Or.inr rfl,?_⟩
    unfold hashGetTail
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    simp only [flag]
    simpa [evaluateHOLFiniteState_skip] using returned

#print axioms source_hashGet_body
#print axioms evaluate_hashGetTail
end InitECandidate.Runtime
