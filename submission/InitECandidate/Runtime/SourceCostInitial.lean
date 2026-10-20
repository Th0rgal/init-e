import InitECandidate.Runtime.SourceCostPipelineFacts
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-! The end-to-end transfer instantiated at the initial states of the pinned
`pan_to_word` `state_rel_imp_semantics` proof: the `pan_globals` target state,
`crepStateHOL` and `loopStateHOL`, built from the source state and the Word
target state. -/

/-- The `pan_globals` target state of the pinned proof, at the given clock. -/
noncomputable def initialGlobalState {F C : Type} (source : PanSemStateFiniteExact 64 F)
    (target : WordSemStateFiniteExact 64 C F) (globalsSize clock : Nat) : PanSemStateFiniteExact 64 F :=
  { ({ source with clock := clock } : PanSemStateFiniteExact 64 F) with
    topAddr := source.topAddr + panBytesInWord 64 * BitVec.ofNat 64 globalsSize
    memaddrs := fun address => source.memaddrs address ∨
      Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
    memory := wlocWlabHOL ∘ target.memory
    locals := source.locals }

theorem initial_globals_premises {F C : Type} (source : PanSemStateFiniteExact 64 F)
    (target : WordSemStateFiniteExact 64 C F) (code : List (DeclHOL 64)) (globalsSize clock : Nat)
    (hmem : ∀ address, source.memaddrs address →
      target.memory address = wlabWlocExact (source.memory address))
    (hstc : decsStcnamesHOLExact (width := 64) [] code = some [])
    (hsize : globalsSize = ((decShapesHOL code).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact (width := 64) [] code)))).sum)
    (hdist : ((functionsHOL code).map Prod.fst).Nodup)
    (halign : panGlobalsByteAlignedHOL source.topAddr) (halloc : globalsAllocatableHOL source code)
    (hcode : source.code = HolFiniteMapExact.empty) (hglobals : source.globals = HolFiniteMapExact.empty)
    (hdim : goodDimindex 64)
    (structFree : Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code) =
      panSimpDeclsHOL code) :
    ((functionsHOL (panSimpDeclsHOL code)).map Prod.fst).Nodup ∧
      initialGlobalState source target globalsSize clock =
        { ({ source with clock := clock } : PanSemStateFiniteExact 64 F) with
          topAddr := source.topAddr + panBytesInWord 64 * BitVec.ofNat 64 globalsSize
          memaddrs := fun address => source.memaddrs address ∨
            Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
          memory := wlocWlabHOL ∘ target.memory
          locals := source.locals } ∧
      source.code = HolFiniteMapExact.empty ∧
      source.globals = HolFiniteMapExact.empty ∧
      panGlobalsByteAlignedHOL source.topAddr ∧
      goodDimindex 64 ∧
      panBytesInWord 64 * BitVec.ofNat 64 globalsSize = panBytesInWord 64 *
        BitVec.ofNat 64 ((decShapesHOL (panSimpDeclsHOL code)).map sizeOfShapeHOL).sum ∧
      Compiler.Backend.StackRemove.addresses source.topAddr globalsSize =
        Compiler.Backend.StackRemove.addresses source.topAddr
          ((decShapesHOL (panSimpDeclsHOL code)).map sizeOfShapeHOL).sum ∧
      (∀ address, source.memaddrs address →
        ¬ Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address) ∧
      (∀ address, source.memaddrs address → source.memory address = (wlocWlabHOL ∘ target.memory) address) ∧
      ¬ source.memaddrs (source.topAddr + panBytesInWord 64 * BitVec.ofNat 64 globalsSize) ∧
      (panBytesInWord 64).toNat * ((decShapesHOL (panSimpDeclsHOL code)).map sizeOfShapeHOL).sum < 2 ^ 64 ∧
      (∀ d ∈ panSimpDeclsHOL code,
        isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true) := by
  have hsizePlain : ((decShapesHOL (panSimpDeclsHOL code)).map sizeOfShapeHOL).sum = globalsSize := by
    rw [hsize, decShapesCompileProgHOL, hstc]
    simp only [holThe]
    congr 1
    apply List.map_congr_left
    intro shape _
    exact (sharp_size_nil shape).symm
  have halloc' := halloc
  dsimp only [globalsAllocatableHOL] at halloc'
  rw [← hsize] at halloc'
  obtain ⟨_, hdisjoint, htopnot, hbound⟩ := halloc'
  refine ⟨?_, rfl, hcode, hglobals, halign, hdim, by rw [hsizePlain], by rw [hsizePlain],
    fun address hs hf => hdisjoint address ⟨hs, hf⟩, ?_, htopnot, ?_, ?_⟩
  · rw [← structFree, functionNamesStructsCompileTopHOL, functionNamesCompileProgHOL]; exact hdist
  · intro address ha
    simp only [Function.comp_apply, hmem address ha, wlocWlabWlabWlocHOL]
  · simpa [hsizePlain, panBytesInWord, Compiler.Backend.StackRemove.bytesInWord, Nat.mul_comm] using hbound
  · rw [← structFree]; exact Pancake.PanStructs.CompileShapeExact.compileTopNoNames _

#print axioms initial_globals_premises
end InitECandidate.Runtime.FineCost
