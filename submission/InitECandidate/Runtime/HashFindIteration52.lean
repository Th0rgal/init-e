import InitECandidate.Runtime.HashFindIteration32
import InitECandidate.Runtime.MemeqCall52
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An occupied-slot lookup iteration executes the actual comparison call
and either returns its index or advances the probe, using exactly one clock. -/
theorem evaluate_hashFind_iteration52 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (a b index capacity : BitVec 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [hashFindComparisonAddress,.var .local (ofString "key"),.var .local (ofString "klen")] =
        some [.val (.word a),.val (.word b),.val (.word (52 : BitVec 64))])
    (code : state.code = originalRuntimeCode) (clock : state.clock ≠ 0)
    (aAligned : a.toNat % 8 = 0) (bAligned : b.toNat % 8 = 0)
    (wordDomain : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat),
      state.memaddrs (a + BitVec.ofNat 64 offset) ∧ state.memaddrs (b + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset ∈ ([48,49,50,51] : List Nat),
      state.memaddrs (panByteAlignHOL (a + BitVec.ofNat 64 offset)) ∧
      state.memaddrs (panByteAlignHOL (b + BitVec.ofNat 64 offset)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity))) :
    ∃ result post, evaluateHOLFiniteState state hashFindIteration = (result,post) ∧
      (result = none ∨ result = some (.returned (.val (.word index)))) ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (result = none → post.locals.lookup (ofString "i") = some (.val (.word (hashProbeNext index capacity)))) ∧
      (result = none → post.locals = (setVarHOLFinite (ofString "i")
        (.val (.word (hashProbeNext index capacity))) state).locals) := by
  obtain ⟨value,ready,boolean,ticks,memory,locals,globals,postCode,addresses,endian,decl⟩ :=
    evaluate_memeq52_declaration state _ _ _ a b arguments code clock aAligned bAligned wordDomain byteDomain
  let entered := setVarHOLFinite (ofString "eq") (.val (.word value)) ready
  have ni : ofString "eq" ≠ ofString "i" := by decide
  have nc : ofString "eq" ≠ ofString "cap" := by decide
  have i : entered.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ni,locals] using indexLocal
  have c : entered.locals.lookup (ofString "cap") = some (.val (.word capacity)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nc,locals] using capLocal
  have e : entered.locals.lookup (ofString "eq") = some (.val (.word value)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  unfold hashFindIteration
  rw [decl]
  rcases boolean with zero | one
  · have run := evaluate_hashFind_mismatch entered index capacity i c (by rw [zero] at e; exact e)
    change ∃ result post, (let output := evaluateHOLFiniteState entered hashFindDecision; _) = _ ∧ _
    rw [run]
    refine ⟨none,_,rfl,Or.inl rfl,ticks,memory,globals,postCode,addresses,endian,?_⟩
    constructor
    · intro _
      rw [restore_other_local _ (ofString "eq") (ofString "i") _ (by decide)]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro _
      change HolFiniteMapExact.resVarEq
        ((ready.locals.update (ofString "eq",.val (.word value))).update
          (ofString "i",.val (.word (hashProbeNext index capacity))))
        (ofString "eq",state.locals.lookup (ofString "eq")) = _
      rw [locals]
      exact restore_updated_other_local state.locals (ofString "eq") (ofString "i") _ _ ni
  · have nonzero : value ≠ 0 := by rw [one]; decide
    have run := evaluate_hashFind_match entered index value nonzero i e
    change ∃ result post, (let output := evaluateHOLFiniteState entered hashFindDecision; _) = _ ∧ _
    rw [run]
    refine ⟨_,_,rfl,Or.inr rfl,ticks,memory,globals,postCode,addresses,endian,?_⟩
    constructor <;> intro impossible <;> cases impossible

#print axioms source_htabFind_iteration
#print axioms evaluate_hashFind_iteration52
end InitECandidate.Runtime
