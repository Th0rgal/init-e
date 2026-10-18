import InitECandidate.Runtime.KeccakShortAfterStateZeroBound
import InitECandidate.Runtime.KeccakShortRemainderBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem evaluate_keccak_short_after_state_zero_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output : BitVec 64)
    (stp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (p : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (n : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (code : state.code = originalRuntimeCode) (ticks : size.toNat + 157 ≤ state.clock)
    (small : pad.toNat + 136 ≤ 33806089496)
    (padAligned : pad.toNat % 8 = 0) (sourceAligned : source.toNat % 8 = 0)
    (outputAligned : output.toNat % 8 = 0)
    (shortInput : size.toNat < 136)
    (bytes : ∀ offset : Nat, offset < 136 → state.memaddrs (panByteAlignHOL (pad + BitVec.ofNat 64 offset)))
    (sourceBytes : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL (source + BitVec.ofNat 64 offset))) :
    ∃ result post, evaluateHOLFiniteState state (stateInitSpineDrop 2 (sourceFunctionBody Guest.guestFn_keccak256)) = (result,post) ∧
      state.clock ≤ post.clock + size.toNat + 157 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  let indexed := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  let entered := setVarHOLFinite (ofString "rem") (.val (.word size)) indexed
  have initial : indexed.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [indexed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atN : indexed.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simpa [indexed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "n" from by decide] using n
  have kept : ∀ name, name ≠ ofString "i" → name ≠ ofString "rem" → entered.locals.lookup name = state.locals.lookup name := by
    intro name ni nr
    simp [entered,indexed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm ni,Ne.symm nr]
  obtain ⟨result,post,run,cost,remaining,noTimeout⟩ :=
    evaluate_keccak_short_remainder_tail_bounded_cells entered pointer pad source size output
      (by rw [kept _ (by decide) (by decide)]; exact stp) padGlobal
      (by rw [kept _ (by decide) (by decide)]; exact p)
      (by simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "rem" ≠ ofString "i" from by decide] using initial)
      (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
      (by rw [kept _ (by decide) (by decide)]; exact outLocal)
      code ticks small padAligned sourceAligned outputAligned shortInput bytes sourceBytes
  have full : evaluateHOLFiniteState state (stateInitSpineDrop 2 (sourceFunctionBody Guest.guestFn_keccak256)) =
      (result,{post with locals := HolFiniteMapExact.resVarEq (HolFiniteMapExact.resVarEq post.locals (ofString "rem",indexed.locals.lookup (ofString "rem"))) (ofString "i",state.locals.lookup (ofString "i"))}) := by
    rw [source_keccak_after_state_zero,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let output := evaluateHOLFiniteState indexed (.seq keccakMainLoop keccakRemainderScope); _) = _
    rw [evaluate_keccak_short_remainder indexed size atN initial shortInput]
    change (let output := evaluateHOLFiniteState entered keccakRemainderTail; _) = _
    rw [run]
  exact ⟨result,_,full,cost,remaining,noTimeout⟩

#print axioms evaluate_keccak_short_after_state_zero_bounded_cells
end InitECandidate.Runtime
