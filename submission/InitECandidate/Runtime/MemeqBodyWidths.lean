import InitECandidate.Runtime.MemeqBody32
import InitECandidate.Runtime.MemeqSelectWidths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Complete original memeq body for aligned20-byte keys: a Boolean result,
zero clocks, and unchanged memory, globals and execution metadata. -/
theorem evaluate_source_memeq20 {F : Type} (state : PanSemStateFiniteExact 64 F) (a b : BitVec 64)
    (aLocal : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word (20 : BitVec 64))))
    (aAligned : a.toNat % 8 = 0) (bAligned : b.toNat % 8 = 0)
    (wordDomain : ∀ offset ∈ ([0,8] : List Nat),
      state.memaddrs (a + BitVec.ofNat 64 offset) ∧ state.memaddrs (b + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset ∈ ([16,17,18,19] : List Nat),
      state.memaddrs (panByteAlignHOL (a + BitVec.ofNat 64 offset)) ∧
      state.memaddrs (panByteAlignHOL (b + BitVec.ofNat 64 offset))) :
    ∃ value : BitVec 64, ∃ post, (value = 0 ∨ value = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memeq) = (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have na : ofString "i" ≠ ofString "a" := by decide
  have nb : ofString "i" ≠ ofString "b" := by decide
  have nn : ofString "i" ≠ ofString "n" := by decide
  have a' : entered.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,na] using aLocal
  have b' : entered.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nb] using bLocal
  have n' : entered.locals.lookup (ofString "n") = some (.val (.word (20 : BitVec 64))) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nn] using sizeLocal
  have aligned := eval_memeq_alignment entered a b a' b' aAligned bAligned
  obtain ⟨value,boolean,run⟩ := evaluate_memeq_aligned20 entered a b a' b' n' wordDomain byteDomain
  have selected : evaluateHOLFiniteState entered
      (.seq (.ite memeqAlignmentCondition memeqAlignedBody .skip) memeqAfterAligned) =
      (some (.returned (.val (.word value))),emptyLocalsHOLFinite entered) := by
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,aligned]
    simp only [show ¬(1 : BitVec 64) = 0 by decide,run]
    rfl
  rw [source_memeq_scoped_body,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact]
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk,selected]
  exact ⟨value,_,boolean,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Complete original memeq body for aligned52-byte keys: a Boolean result,
zero clocks, and unchanged memory, globals and execution metadata. -/
theorem evaluate_source_memeq52 {F : Type} (state : PanSemStateFiniteExact 64 F) (a b : BitVec 64)
    (aLocal : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word (52 : BitVec 64))))
    (aAligned : a.toNat % 8 = 0) (bAligned : b.toNat % 8 = 0)
    (wordDomain : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat),
      state.memaddrs (a + BitVec.ofNat 64 offset) ∧ state.memaddrs (b + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset ∈ ([48,49,50,51] : List Nat),
      state.memaddrs (panByteAlignHOL (a + BitVec.ofNat 64 offset)) ∧
      state.memaddrs (panByteAlignHOL (b + BitVec.ofNat 64 offset))) :
    ∃ value : BitVec 64, ∃ post, (value = 0 ∨ value = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memeq) = (some (.returned (.val (.word value))),post) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have na : ofString "i" ≠ ofString "a" := by decide
  have nb : ofString "i" ≠ ofString "b" := by decide
  have nn : ofString "i" ≠ ofString "n" := by decide
  have a' : entered.locals.lookup (ofString "a") = some (.val (.word a)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,na] using aLocal
  have b' : entered.locals.lookup (ofString "b") = some (.val (.word b)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nb] using bLocal
  have n' : entered.locals.lookup (ofString "n") = some (.val (.word (52 : BitVec 64))) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nn] using sizeLocal
  have aligned := eval_memeq_alignment entered a b a' b' aAligned bAligned
  obtain ⟨value,boolean,run⟩ := evaluate_memeq_aligned52 entered a b a' b' n' wordDomain byteDomain
  have selected : evaluateHOLFiniteState entered
      (.seq (.ite memeqAlignmentCondition memeqAlignedBody .skip) memeqAfterAligned) =
      (some (.returned (.val (.word value))),emptyLocalsHOLFinite entered) := by
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,aligned]
    simp only [show ¬(1 : BitVec 64) = 0 by decide,run]
    rfl
  rw [source_memeq_scoped_body,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact]
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
    simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk,selected]
  exact ⟨value,_,boolean,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms evaluate_source_memeq20
#print axioms evaluate_source_memeq52
end InitECandidate.Runtime
