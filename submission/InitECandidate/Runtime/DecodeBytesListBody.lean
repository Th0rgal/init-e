import InitECandidate.Runtime.DecodeBytesListAfterSplit
import InitECandidate.Runtime.PanThreeWordShapeLookup
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem sszSplitReturned_count {σ : Type} (entry post : PanSemStateFiniteExact 64 σ) (len lim pointer : BitVec 64)
    (v : ValueHOL 64) (h : SszSplitVarListReturned entry len lim pointer v post) :
    ∃ arr count : BitVec 64, v = .rStruct [.val (.word arr), .val (.word count)] ∧
      count.toNat ≤ len.toNat / 4 ∧ count.toNat < 2 ^ 62 := by
  rcases h with ⟨_, hv, _⟩ | ⟨_, first, _, ok, hv, _⟩
  · exact ⟨0, 0, hv, by simp, by simp⟩
  · refine ⟨pointer, first >>> (2 : Nat), hv, ?_, ?_⟩
    · have firstLe : first.toNat ≤ len.toNat := by have := ok.2.2; rw [BitVec.lt_def] at this; omega
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.div_le_div_right firstLe
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := first.isLt; omega

def bytesListSplitLocals (p len lim : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  ((HolFiniteMapExact.empty.update (ofString "p",.val (.word p))).update
    (ofString "len",.val (.word len))).update (ofString "lim",.val (.word lim))

def bytesListBound (len : BitVec 64) : Nat := sszSplitBound len + 1 + 2 * (len.toNat / 4)

/-- Returned decode_bytes_list: the actual split body returned v at the callee
entry with all split contracts, the outer post frame equals the split post,
and every slice length cell is at most maxb. -/
def DecodeBytesListReturned {σ : Type} (e : PanSemStateFiniteExact 64 σ) (p len lim maxb pointer : BitVec 64)
    (v : ValueHOL 64) (out : PanSemStateFiniteExact 64 σ) : Prop :=
  ∃ (entryClock : Nat) (bodyPost : PanSemStateFiniteExact 64 σ),
    let entry := ({callEntryStateHOLFinite e (bytesListSplitLocals p len lim) with clock := entryClock} :
      PanSemStateFiniteExact 64 σ)
    evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_ssz_split_var_list) = (some (.returned v), bodyPost) ∧
    SszSplitVarListReturned entry len lim pointer v bodyPost ∧ SszSplitVarListSlicesReturned entry p len pointer bodyPost ∧
    out.memory = bodyPost.memory ∧ out.globals = bodyPost.globals ∧ out.memaddrs = bodyPost.memaddrs ∧
    ∀ arr count : BitVec 64, v = .rStruct [.val (.word arr), .val (.word count)] →
      ∀ k : BitVec 64, k.toNat < count.toNat → BytesListItemOK bodyPost.memaddrs bodyPost.memory arr maxb k

theorem evaluate_decodeBytesList_body_enough {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (p len lim maxb pointer : BitVec 64) (installed : e.code = originalRuntimeCode)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word len)))
    (hlim : e.locals.lookup (ofString "lim") = some (.val (.word lim)))
    (hmaxb : e.locals.lookup (ofString "maxb") = some (.val (.word maxb)))
    (heap : e.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (enough : bytesListBound len ≤ e.clock) :
    let out := evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_decode_bytes_list)
    e.clock ≤ out.2.clock + bytesListBound len ∧ out.2.clock ≤ e.clock ∧ out.1 ≠ none ∧ out.1 ≠ some .timeOut ∧
      (∀ v, out.1 = some (.returned v) → DecodeBytesListReturned e p len lim maxb pointer v out.2) := by
  unfold bytesListBound at enough ⊢
  have rm : ofString "r" ≠ ofString "maxb" := by decide_cbv
  have args : evalListHOLFinite e (h := fun address => Classical.propDecidable (e.memaddrs address))
      [sszLocal "p", sszLocal "len", sszLocal "lim"] = some [.val (.word p), .val (.word len), .val (.word lim)] := by
    simp [sszLocal, evalListHOLFinite, evalListHOLExact, evalHOLExact, hp, hlen, hlim]
  have lookup := pan_three_word_shape_lookup e.code.lookup (ofString "ssz_split_var_list")
    (ofString "p") (ofString "len") (ofString "lim") (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
    (.comb [.one,.one]) p len lim (by decide_cbv) (by decide_cbv) (by decide_cbv)
    (by rw [installed]; exact originalRuntimeCode_sszSplitVarList_lookup)
  let entry := callEntryStateHOLFinite e (bytesListSplitLocals p len lim)
  have ep : entry.locals.lookup (ofString "p") = some (.val (.word p)) := by
    simp [entry, bytesListSplitLocals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "len" ≠ ofString "p" by decide_cbv, show ofString "lim" ≠ ofString "p" by decide_cbv]
  have el : entry.locals.lookup (ofString "len") = some (.val (.word len)) := by
    simp [entry, bytesListSplitLocals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "lim" ≠ ofString "len" by decide_cbv]
  have elim : entry.locals.lookup (ofString "lim") = some (.val (.word lim)) := by
    simp [entry, bytesListSplitLocals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have bounded := evaluate_sszSplitVarList_body entry p len lim pointer installed ep el elim heap pointerBound
  have slices := evaluate_sszSplitVarList_slices entry p len lim pointer installed ep el elim heap pointerBound
  rw [source_decodeBytesList_body, evaluateHOLFiniteState_decCall_total, args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg (by omega), fixClockHOLFinite_evaluateState]
  have entryClock : entry.clock = e.clock - 1 := rfl
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite e (((HolFiniteMapExact.empty.update
      (ofString "p",.val (.word p))).update (ofString "len",.val (.word len))).update (ofString "lim",.val (.word lim))))
      (sourceFunctionBody Guest.guestFn_ssz_split_var_list) with
  | mk result middle =>
    have run' : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_ssz_split_var_list) =
        (result, middle) := run
    rw [run'] at bounded slices
    dsimp only at bounded slices
    obtain ⟨b1, b2, b3, b4, b5⟩ := bounded
    rw [entryClock] at b1 b2
    have nt := b3 (by unfold sszSplitBound at enough ⊢; omega)
    cases result with
    | none => exact absurd rfl b4
    | some result =>
      cases result
      case returned value =>
        obtain ⟨arr, count, hv, cntLe, cntSmall⟩ := sszSplitReturned_count entry middle len lim pointer value (b5 value rfl)
        subst hv
        simp only [shapeOfHOLExact, shapeEqHOL, List.map, Bool.and_self, if_true]
        have sh : shapeEqHOL.shapeEqListHOL [ShapeHOL.one, ShapeHOL.one] [ShapeHOL.one, ShapeHOL.one] = true := by
          simp [shapeEqHOL.shapeEqListHOL, shapeEqHOL]
        rw [if_pos sh]
        have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
        rw [run'] at metadata
        generalize ht : setVarHOLFinite (ofString "r") (.rStruct [.val (.word arr), .val (.word count)])
          ({middle with locals := e.locals} : PanSemStateFiniteExact 64 σ) = t
        have tr : t.locals.lookup (ofString "r") = some (.rStruct [.val (.word arr), .val (.word count)]) := by
          rw [← ht]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        have tm : t.locals.lookup (ofString "maxb") = some (.val (.word maxb)) := by
          rw [← ht]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, rm, hmaxb]
        have tc : t.clock = middle.clock := by rw [← ht]; rfl
        have tmem : t.memory = middle.memory := by rw [← ht]; rfl
        have tdom : t.memaddrs = middle.memaddrs := by rw [← ht]; rfl
        have tg : t.globals = middle.globals := by rw [← ht]; rfl
        have tcode : t.code = originalRuntimeCode := by rw [← ht]; exact metadata.1.trans installed
        obtain ⟨a1, a2, a3, a4, a5⟩ := evaluate_bytesListAfterSplit t arr count maxb tr tm tcode cntSmall
          (by unfold sszSplitBound at enough b1; omega)
        dsimp only
        refine ⟨by omega, by omega, a3, a4, fun v h => ?_⟩
        obtain ⟨hv, om, og, od, items⟩ := a5 v h
        subst hv
        refine ⟨e.clock - 1, middle, run', b5 _ rfl, slices _ rfl, om.trans tmem, og.trans tg, od.trans tdom, ?_⟩
        intro arr' count' heq k lt
        simp only [ValueHOL.rStruct.injEq, List.cons.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq,
          and_true] at heq
        obtain ⟨rfl, rfl⟩ := heq
        rw [← tmem, ← tdom]
        exact items k lt
      all_goals exact ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega,
        by simp, by first | exact fun h => nt (by simpa using h) | simp, fun v h => by simp at h⟩

#print axioms evaluate_decodeBytesList_body_enough

/-- The actual decode_bytes_list body at any clock: at most
sszSplitBound len + 1 + 2*(len/4) clocks, no timeout with that clock, never
none, and every return satisfies the split/slice/item-size contract. -/
theorem evaluate_decodeBytesList_body {σ : Type} (e : PanSemStateFiniteExact 64 σ)
    (p len lim maxb pointer : BitVec 64) (installed : e.code = originalRuntimeCode)
    (hp : e.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : e.locals.lookup (ofString "len") = some (.val (.word len)))
    (hlim : e.locals.lookup (ofString "lim") = some (.val (.word lim)))
    (hmaxb : e.locals.lookup (ofString "maxb") = some (.val (.word maxb)))
    (heap : e.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) :
    let out := evaluateHOLFiniteState e (sourceFunctionBody Guest.guestFn_decode_bytes_list)
    e.clock ≤ out.2.clock + bytesListBound len ∧ out.2.clock ≤ e.clock ∧
      (bytesListBound len ≤ e.clock → out.1 ≠ some .timeOut) ∧ out.1 ≠ none ∧
      (∀ v, out.1 = some (.returned v) → DecodeBytesListReturned e p len lim maxb pointer v out.2) := by
  by_cases enough : bytesListBound len ≤ e.clock
  · obtain ⟨a, b, c, d, f⟩ := evaluate_decodeBytesList_body_enough e p len lim maxb pointer installed hp hlen hlim
      hmaxb heap pointerBound enough
    exact ⟨a, b, fun _ => d, c, f⟩
  · intro out
    have lower := evaluateHOLFiniteState_clock_le e (sourceFunctionBody Guest.guestFn_decode_bytes_list)
    let lifted : PanSemStateFiniteExact 64 σ := {e with clock := e.clock + bytesListBound len}
    have high := evaluate_decodeBytesList_body_enough lifted p len lim maxb pointer installed hp hlen hlim hmaxb heap
      pointerBound (by simp [lifted])
    have same : out.1 ≠ some .timeOut →
        evaluateHOLFiniteState lifted (sourceFunctionBody Guest.guestFn_decode_bytes_list) =
          (out.1, {out.2 with clock := out.2.clock + bytesListBound len}) :=
      fun nt => panPropsEvaluateAddClockEq _ e out.1 out.2 _ ⟨rfl, nt⟩
    refine ⟨by omega, lower, fun h => absurd h enough, ?_, ?_⟩
    · intro none_
      have run := same (by rw [none_]; simp)
      exact high.2.2.1 (by rw [run]; exact none_)
    · intro v returned
      have run := same (by rw [returned]; simp)
      have contract := high.2.2.2.2 v (by rw [run]; exact returned)
      rw [run] at contract
      obtain ⟨c, bodyPost, r1, r2, r3, r4, r5, r6, r7⟩ := contract
      exact ⟨c, bodyPost, r1, r2, r3, r4, r5, r6, r7⟩

#print axioms evaluate_decodeBytesList_body
end InitECandidate.Runtime
