import InitECandidate.Runtime.KeccakShortAfterStateZeroBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original state zeroing and short-input suffix have total source
clock cost at most n+358, including exceptional absorption/output outcomes. -/
theorem evaluate_keccak_short_state_prefix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output : BitVec 64)
    (stp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (p : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (n : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (code : state.code = originalRuntimeCode) (ticks : size.toNat + 358 ≤ state.clock)
    (stateSmall : pointer.toNat + 200 ≤ 33806089496)
    (stateAligned : pointer.toNat % 8 = 0)
    (stateWords : ∀ offset : Nat, offset < 200 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (stateBytes : ∀ offset : Nat, offset < 200 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (small : pad.toNat + 136 ≤ 33806089496)
    (padAligned : pad.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (outputAligned : output.toNat % 8 = 0)
    (shortInput : size.toNat < 136)
    (words : ∀ offset : Nat, offset < 136 → state.memaddrs (pad + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < 136 → state.memaddrs (panByteAlignHOL (pad + BitVec.ofNat 64 offset)))
    (sourceWords : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset))) :
    ∃ result post, evaluateHOLFiniteState state (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_keccak256)) = (result,post) ∧
      state.clock ≤ post.clock + size.toNat + 358 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  obtain ⟨middle,run,_,cost,remaining,globals,locals,postCode,domain,_⟩ :=
    evaluate_keccak_state_zero_prefix state pointer stp code (by omega) stateSmall stateAligned stateWords stateBytes
  obtain ⟨result,post,tail,tailCost,tailRemaining,noTimeout⟩ :=
    evaluate_keccak_short_after_state_zero_bounded middle pointer pad source size output
      (by rw [locals]; exact stp) (by rw [globals]; exact padGlobal)
      (by rw [locals]; exact p) (by rw [locals]; exact n)
      (by rw [locals]; exact outLocal) (postCode.trans code) (by omega)
      small padAligned sourceAligned outputAligned shortInput
      (by intro offset inside; rw [domain]; exact words offset inside)
      (by intro offset inside; rw [domain]; exact bytes offset inside)
      (by intro offset inside; rw [domain]; exact sourceWords offset inside)
      (by intro offset inside; rw [domain]; exact sourceBytes offset inside)
  exact ⟨result,post,run.trans tail,by omega,by omega,noTimeout⟩

theorem source_keccak_body : sourceFunctionBody Guest.guestFn_keccak256 =
    .dec (ofString "stp") .one (.var .global (ofString "keccak_st"))
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_keccak256)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The complete original Keccak body for aligned short input/output costs
at most n+358 source ticks; this is a runtime bound, not a digest specification. -/
theorem evaluate_keccak_short_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output : BitVec 64)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (p : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (n : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (code : state.code = originalRuntimeCode) (ticks : size.toNat + 358 ≤ state.clock)
    (stateSmall : pointer.toNat + 200 ≤ 33806089496)
    (stateAligned : pointer.toNat % 8 = 0)
    (stateWords : ∀ offset : Nat, offset < 200 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (stateBytes : ∀ offset : Nat, offset < 200 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (small : pad.toNat + 136 ≤ 33806089496)
    (padAligned : pad.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (outputAligned : output.toNat % 8 = 0)
    (shortInput : size.toNat < 136)
    (words : ∀ offset : Nat, offset < 136 → state.memaddrs (pad + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < 136 → state.memaddrs (panByteAlignHOL (pad + BitVec.ofNat 64 offset)))
    (sourceWords : ∀ offset : Nat, offset < size.toNat → state.memaddrs (source + BitVec.ofNat 64 offset))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset))) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_keccak256) = (result,post) ∧
      state.clock ≤ post.clock + size.toNat + 358 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "stp") (.val (.word pointer)) state
  have stp : entered.locals.lookup (ofString "stp") = some (.val (.word pointer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have kept : ∀ name, name ≠ ofString "stp" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  obtain ⟨result,post,run,cost,remaining,noTimeout⟩ :=
    evaluate_keccak_short_state_prefix_bounded entered pointer pad source size output stp padGlobal
      (by rw [kept _ (by decide)]; exact p) (by rw [kept _ (by decide)]; exact n)
      (by rw [kept _ (by decide)]; exact outLocal) code ticks
      stateSmall stateAligned stateWords stateBytes small padAligned sourceAligned outputAligned shortInput
      words bytes sourceWords sourceBytes
  have full : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_keccak256) =
      (result,{post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "stp",state.locals.lookup (ofString "stp"))}) := by
    rw [source_keccak_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,stateGlobal,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let output := evaluateHOLFiniteState entered (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_keccak256)); _) = _
    rw [run]
  exact ⟨result,_,full,cost,remaining,noTimeout⟩

#print axioms evaluate_keccak_short_state_prefix_bounded
#print axioms source_keccak_body
#print axioms evaluate_keccak_short_body_bounded
end InitECandidate.Runtime
