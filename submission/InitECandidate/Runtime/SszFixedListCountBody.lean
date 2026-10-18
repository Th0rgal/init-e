import InitECandidate.Runtime.SszFixedListCountTail
import InitECandidate.Runtime.PanTwoWordShapeLookup
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual ssz_fixed_list_count body for a nonzero element size: at most
66 source clocks including the udivmod call and a rejection call, terminal,
and any return is the exact element count with no remainder and within lim. -/
theorem evaluate_sszFixedListCount_body {σ : Type} (e : PanSemStateFiniteExact 64 σ) (len sz lim : BitVec 64)
    (installed : e.code = originalRuntimeCode)
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word len)))
    (hsz : e.locals.lookup (ofString "sz") = some (.val (.word sz)))
    (hlim : e.locals.lookup (ofString "lim") = some (.val (.word lim))) (nz : sz ≠ 0) :
    let out := evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)
    e.clock ≤ out.2.clock + 66 ∧ out.2.clock ≤ e.clock ∧ (66 ≤ e.clock → out.1 ≠ some .timeOut) ∧
      out.1 ≠ none ∧
      (∀ v, out.1 = some (.returned v) → v = .val (.word (len / sz)) ∧ len % sz = 0 ∧ ¬ lim < len / sz) := by
  have args : evalListHOLFinite e (h := fun address => Classical.propDecidable (e.memaddrs address))
      [.var .local (ofString "len"), .var .local (ofString "sz")] = some [.val (.word len), .val (.word sz)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hlen, hsz]
  have names : ofString "a" ≠ ofString "b" := by decide_cbv
  have lookup := pan_two_word_lookup_shape e.code.lookup (ofString "udivmod") (ofString "a") (ofString "b")
    (sourceFunctionBody Guest.guestFn_udivmod) (.comb [.one,.one]) len sz names
    (by rw [installed]; exact originalRuntimeCode_udivmod_lookup)
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "a",.val (.word len))).update (ofString "b",.val (.word sz))
  have ca : (callEntryStateHOLFinite e callee).locals.lookup (ofString "a") = some (.val (.word len)) := by
    simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm names]
  have cb : (callEntryStateHOLFinite e callee).locals.lookup (ofString "b") = some (.val (.word sz)) := by
    simp [callEntryStateHOLFinite, callee, HolFiniteMapExact.lookup_update, FUPDATE]
  have body := evaluate_udivmod_body (callEntryStateHOLFinite e callee) len sz ca cb nz
  have lower := evaluateHOLFiniteState_clock_le e (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)
  rw [source_sszFixedListCount_body] at lower ⊢
  rw [evaluateHOLFiniteState_decCall_total, args]
  dsimp only
  rw [lookup]
  dsimp only
  by_cases zero : e.clock = 0
  · simp only [zero, if_true]
    refine ⟨by simp [emptyLocalsHOLFinite], by simp [emptyLocalsHOLFinite, zero], fun h => by omega, by simp, ?_⟩
    intro v h; simp at h
  · rw [if_neg zero]
    rw [fixClockHOLFinite_evaluateState]
    have entryClock : (callEntryStateHOLFinite e callee).clock = e.clock - 1 := rfl
    cases run : evaluateHOLFiniteState (callEntryStateHOLFinite e callee) (sourceFunctionBody Guest.guestFn_udivmod) with
    | mk result middle =>
      rw [run] at body
      dsimp only at body
      rw [entryClock] at body
      obtain ⟨c1, c2, noTimeout, returnedValue⟩ := body
      cases result with
      | none => exact ⟨by simp; omega, by simp; omega, fun _ => by simp, by simp, fun v h => by simp at h⟩
      | some result =>
        cases result
        case returned value =>
          obtain rfl := returnedValue value rfl
          simp only [shapeOfHOLExact, shapeEqHOL, List.map, Bool.and_self, if_true]
          have sh : shapeEqHOL.shapeEqListHOL [ShapeHOL.one, ShapeHOL.one] [ShapeHOL.one, ShapeHOL.one] = true := by simp [shapeEqHOL.shapeEqListHOL, shapeEqHOL]
          rw [if_pos sh]
          have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite e callee)
            (sourceFunctionBody Guest.guestFn_udivmod)
          rw [run] at metadata
          have qrName : ofString "lim" ≠ ofString "qr" := by decide_cbv
          let c := setVarHOLFinite (ofString "qr")
            (.rStruct [.val (.word (len / sz)), .val (.word (len % sz))]) {middle with locals := e.locals}
          have cCode : c.code = originalRuntimeCode := metadata.1.trans installed
          have hqr : c.locals.lookup (ofString "qr") =
              some (.rStruct [.val (.word (len / sz)), .val (.word (len % sz))]) := by
            simp [c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
          have hlim' : c.locals.lookup (ofString "lim") = some (.val (.word lim)) := by
            simp [c, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, qrName, Ne.symm qrName, hlim]
          have tail := evaluate_sszFixedListCountTail c (len / sz) (len % sz) lim cCode hqr hlim'
          have cClock : c.clock = middle.clock := rfl
          change (let out := (let o := evaluateHOLFiniteState c sszFixedListCountTail;
            (o.1, {o.2 with locals := o.2.locals.resVarEq (ofString "qr", e.locals.lookup (ofString "qr"))})); _)
          cases tailRun : evaluateHOLFiniteState c sszFixedListCountTail with
          | mk r2 post2 =>
            rw [tailRun] at tail
            dsimp only at tail ⊢
            rw [cClock] at tail
            obtain ⟨t1, t2, t3, t4, t5⟩ := tail
            refine ⟨by omega, by omega, fun h => t3 (by omega), t4, ?_⟩
            intro v h
            obtain ⟨rfl, rz, rl⟩ := t5 v h
            exact ⟨rfl, rz, rl⟩
        all_goals exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega,
          fun h => by first | exact fun _ => noTimeout (by omega) rfl | simp, by simp, fun v h => by simp at h⟩

#print axioms evaluate_sszFixedListCount_body
end InitECandidate.Runtime
