import InitECandidate.Runtime.MemzeroLoopBound
import InitECandidate.Runtime.OriginalMemzeroCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.DiscardCallNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original memzero body budget, with unrestricted alignment and all memory-error outcomes included. -/
theorem evaluate_memzero_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination size : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (small : size.toNat ≤ 33806089496)
    (budget : size.toNat / 32 + size.toNat / 8 + 10 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memzero) = (result,post) ∧
      state.clock ≤ post.clock + (size.toNat / 32 + size.toNat / 8 + 10) ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have locals : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atIndex : entered.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atSize := (locals _ (by decide)).trans sizeLocal
  obtain ⟨flag,condition⟩ := eval_memzero_alignment_value entered destination
    ((locals _ (by decide)).trans dstLocal)
  obtain ⟨result,post,run,cost,remaining,noTimeout⟩ := evaluate_memzero_after_index_bounded entered 0 size flag
    atIndex atSize (by simp) small condition (by simpa [entered,setVarHOLFinite] using budget)
  let final := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "i",state.locals.lookup (ofString "i"))}
  refine ⟨result,final,?_,?_,remaining,noTimeout⟩
  · rw [source_memzero_scoped_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let result := evaluateHOLFiniteState entered memzeroAfterIndex; _) = _
    rw [run]
  · change state.clock ≤ post.clock + (size.toNat / 32 + size.toNat / 8 + 10)
    simpa [entered,setVarHOLFinite] using cost

#print axioms evaluate_memzero_body_bounded

/-- Actual original memzero discard calls add one clock to the body budget. -/
theorem evaluate_memzero_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (destination size : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word destination),.val (.word size)])
    (code : state.code = originalRuntimeCode) (small : size.toNat ≤ 33806089496)
    (budget : size.toNat / 32 + size.toNat / 8 + 11 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memzero") arguments)
    state.clock ≤ evaluated.2.clock + (size.toNat / 32 + size.toNat / 8 + 11) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "dst",.val (.word destination))).update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have dst : entry.locals.lookup (ofString "dst") = some (.val (.word destination)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "dst" by decide]
  have n : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,run,cost,remaining,noTimeout⟩ := evaluate_memzero_body_bounded entry destination size dst n small
    (by change size.toNat / 32 + size.toNat / 8 + 10 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "memzero") =
      some ([(ofString "dst",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memzero,.one) := by
    rw [code]; exact originalRuntimeCode_memzero_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "memzero") (ofString "dst") (ofString "n")
    (sourceFunctionBody Guest.guestFn_memzero) destination size (by decide) installed
  have clock := evaluate_discard_call_body_clock state post (ofString "memzero") arguments
    [.val (.word destination),.val (.word size)] (sourceFunctionBody Guest.guestFn_memzero) callee .one result args lookup (by omega) run
  have safe := evaluate_discard_call_body_no_timeout state post (ofString "memzero") arguments
    [.val (.word destination),.val (.word size)] (sourceFunctionBody Guest.guestFn_memzero) callee .one result args lookup (by omega) run noTimeout
  dsimp only
  rw [clock]
  have entryClock : entry.clock = state.clock - 1 := rfl
  exact ⟨by omega,by omega,safe⟩

#print axioms evaluate_memzero_call_bounded
end InitECandidate.Runtime
