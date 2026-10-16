import InitECandidate.Runtime.HashFindCall32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashHasTail : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.var .local (ofString "i")) (.load .one (hashLocalAddress (ofString "t") 16)))
    (.return (.const 0)) .skip) (.return (.const 1))

theorem source_hashHas_body : sourceFunctionBody Guest.guestFn_htab_has =
    .decCall (ofString "i") .one (ofString "htab_find_slot")
      [.var .local (ofString "t"),.var .local (ofString "key")] hashHasTail := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual has-table decision reads the capacity sentinel and returns a
Boolean word, with no source-clock or memory effects. -/
theorem evaluate_hashHasTail {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table index capacity : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (domain : state.memaddrs (table + 16)) (cell : state.memory (table + 16) = .word capacity) :
    ∃ value : BitVec 64, (value = 0 ∨ value = 1) ∧ evaluateHOLFiniteState state hashHasTail =
      (some (.returned (.val (.word value))),emptyLocalsHOLFinite state) := by
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashLocalAddress (ofString "t") 16)) = some (.val (.word capacity)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashLocalAddress state (ofString "t") table 16 tableLocal]
    simp [memLoadHOLExact]
    exact ⟨domain,cell⟩
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.var .local (ofString "i")) (.load .one (hashLocalAddress (ofString "t") 16))) =
      some (.val (.word (if Compiler.Encoders.Asm.wordCmpHOL .equal index capacity then 1 else 0))) := by
    have localEval : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) (.var .local (ofString "i")) =
          some (.val (.word index)) := indexLocal
    rw [evalHOLExact,localEval,loaded]
  cases flag : Compiler.Encoders.Asm.wordCmpHOL .equal index capacity with
  | false =>
    refine ⟨1,Or.inr rfl,?_⟩
    unfold hashHasTail
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    simp only [flag]
    simp [evaluateHOLFiniteState_skip,evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  | true =>
    refine ⟨0,Or.inl rfl,?_⟩
    unfold hashHasTail
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
    simp only [flag]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

#print axioms source_hashHas_body
#print axioms evaluate_hashHasTail
end InitECandidate.Runtime
