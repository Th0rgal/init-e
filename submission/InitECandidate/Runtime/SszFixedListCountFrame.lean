import InitECandidate.Runtime.SszBodyFrames
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- ssz_fixed_list_count with a nonzero element size preserves memory and
globals on every continuing outcome, at any clock. -/
theorem evaluate_sszFixedListCount_body_frame {σ : Type} (e : PanSemStateFiniteExact 64 σ) (len sz : BitVec 64)
    (installed : e.code = originalRuntimeCode)
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word len)))
    (hsz : e.locals.lookup (ofString "sz") = some (.val (.word sz))) (nz : sz ≠ 0) :
    SszBenign (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)).1 →
    (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)).2.memory = e.memory ∧
      (evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)).2.globals = e.globals := by
  have args : evalListHOLFinite e (h := fun address => Classical.propDecidable (e.memaddrs address))
      [.var .local (ofString "len"), .var .local (ofString "sz")] = some [.val (.word len), .val (.word sz)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hlen, hsz]
  have names : ofString "a" ≠ ofString "b" := by decide_cbv
  have lookup := pan_two_word_lookup_shape e.code.lookup (ofString "udivmod") (ofString "a") (ofString "b")
    (sourceFunctionBody Guest.guestFn_udivmod) (.comb [.one,.one]) len sz names
    (by rw [installed]; exact originalRuntimeCode_udivmod_lookup)
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "a",.val (.word len))).update (ofString "b",.val (.word sz))
  have cb : (callEntryStateHOLFinite e callee).locals.lookup (ofString "b") = some (.val (.word sz)) := by
    simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE]
  have frame := evaluate_udivmod_body_frame (callEntryStateHOLFinite e callee) sz cb nz
  have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite e callee)
    (sourceFunctionBody Guest.guestFn_udivmod)
  rw [source_sszFixedListCount_body]
  rw [evaluateHOLFiniteState_decCall_total, args]
  dsimp only
  rw [lookup]
  dsimp only
  by_cases zero : e.clock = 0
  · simp only [zero, if_true]
    intro _; exact ⟨rfl, rfl⟩
  · rw [if_neg zero]
    rw [fixClockHOLFinite_evaluateState]
    cases run : evaluateHOLFiniteState (callEntryStateHOLFinite e callee) (sourceFunctionBody Guest.guestFn_udivmod) with
    | mk result middle =>
      rw [run] at frame metadata
      obtain ⟨m, g⟩ := frame
      have mcode : middle.code = originalRuntimeCode := metadata.1.trans installed
      dsimp only
      cases result with
      | none => intro _; exact ⟨m, g⟩
      | some result =>
        cases result
        case returned value =>
          dsimp only
          split
          · intro benign
            dsimp only at benign ⊢
            obtain ⟨tm, tg⟩ := evaluate_sszFailFree_frame sszFixedListCountTail sszFixedListCountTail_failFree _
              (by exact mcode) benign
            exact ⟨tm.trans m, tg.trans g⟩
          · intro _; exact ⟨m, g⟩
        all_goals intro _; exact ⟨m, g⟩

#print axioms evaluate_sszFixedListCount_body_frame
end InitECandidate.Runtime
