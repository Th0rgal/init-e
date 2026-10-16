import InitECandidate.Runtime.MemzeroMemoryFrameStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The four original zero stores preserve a distinct watched word. -/
theorem evaluate_memzero_word32_frame_step {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationDomain : ∀ offset ∈ ([0,8,16,24] : List (BitVec 64)), state.memaddrs (destination + index + offset))
    (separate : ∀ offset ∈ ([0,8,16,24] : List (BitVec 64)), watched ≠ destination + index + offset) :
    ∃ post, evaluateHOLFiniteState state memzeroWord32Body = (none,post) ∧ post.clock = state.clock ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 32))) ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "i" → post.locals.lookup name = state.locals.lookup name) ∧
      post.memory watched = state.memory watched := by
  have run := evaluate_memzero_word32_body state destination index dstLocal indexLocal
    (by simpa using destinationDomain 0 (by simp)) (destinationDomain 8 (by simp))
    (destinationDomain 16 (by simp)) (destinationDomain 24 (by simp))
  have sep0 : watched ≠ destination + index := by simpa using separate 0 (by simp)
  have sep8 := separate 8 (by simp)
  have sep16 := separate 16 (by simp)
  have sep24 := separate 24 (by simp)
  refine ⟨_,run,rfl,?_,rfl,rfl,rfl,rfl,?_,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    simp [setVarHOLFinite,sourceWriteWord,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  · simp only [setVarHOLFinite,sourceWriteWord]
    rw [if_neg sep24,if_neg sep16,if_neg sep8,if_neg sep0]

#print axioms evaluate_memzero_word32_frame_step
end InitECandidate.Runtime
