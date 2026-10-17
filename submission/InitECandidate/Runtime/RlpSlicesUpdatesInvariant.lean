import InitECandidate.Runtime.RlpSlicesAdvances
import InitECandidate.Runtime.PanStoreSequenceNormal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpSlices_updates : rlpSlicesUpdates =
    .seq (.store (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "i"),.const 16]])
      (.op .add [.var .local (ofString "p"),.var .local (ofString "off")]))
      (.seq (.store (.op .add [.var .local (ofString "arr"),.panop .mul [.var .local (ofString "i"),.const 16],.const 8])
        (.var .local (ofString "total"))) rlpSlicesAdvances) := by
  simp only [rlpSlicesUpdates,rlpSlicesAdvances,rlpSlicesStep,rlpSlicesLoop,rlpSlicesLoopAndReturn,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Successful original slice stores preserve locals before the two exact
assignments; every unrelated local survives the complete update block. -/
theorem rlpSlices_updates_normal_locals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index offset total : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (totalLocal : state.locals.lookup (ofString "total") = some (.val (.word total)))
    (run : evaluateHOLFiniteState state rlpSlicesUpdates = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      post.locals.lookup (ofString "off") = some (.val (.word (offset + total))) ∧
      (∀ name, name ≠ ofString "i" → name ≠ ofString "off" → post.locals.lookup name = state.locals.lookup name) := by
  rw [source_rlpSlices_updates] at run
  obtain ⟨first,_,firstLocals,next⟩ := evaluate_store_sequence_normal state post _ _ _ run
  obtain ⟨second,_,secondLocals,advanced⟩ := evaluate_store_sequence_normal first post _ _ _ next
  have locals : second.locals = state.locals := secondLocals.trans firstLocals
  have actual := evaluate_rlpSlices_advances second offset index total
    (by rw [locals]; exact offsetLocal) (by rw [locals]; exact indexLocal) (by rw [locals]; exact totalLocal)
  have postEq := (Prod.mk.inj (advanced.symm.trans actual)).2
  rw [postEq]
  refine ⟨?_,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "off" by decide]
  · intro name differentIndex differentOffset
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm differentIndex,Ne.symm differentOffset,locals]

#print axioms rlpSlices_updates_normal_locals
end InitECandidate.Runtime
