import InitECandidate.Runtime.DecodeRequestsSource
import InitECandidate.Runtime.SszFixedListCountBody
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Clock-bounded, timeout-free execution of a program from every state with
at least the given clock that satisfies a precondition. -/
def ReqBounded {σ : Type} (P : PanSemStateFiniteExact 64 σ → Prop) (prog : ProgHOL 64) (T : Nat) : Prop :=
  ∀ t, P t → T ≤ t.clock → t.clock ≤ (evaluateHOLFiniteState t prog).2.clock + T ∧
    (evaluateHOLFiniteState t prog).2.clock ≤ t.clock ∧ (evaluateHOLFiniteState t prog).1 ≠ some .timeOut

def reqCountLocals (length size : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  ((HolFiniteMapExact.empty.update (ofString "len",.val (.word length))).update
    (ofString "sz",.val (.word size))).update (ofString "lim",.val (.word 9223372036854775807))

theorem reqCount_args {σ : Type} (s : PanSemStateFiniteExact 64 σ) (a b : String) (A B size : BitVec 64)
    (ha : s.locals.lookup (ofString a) = some (.val (.word A)))
    (hb : s.locals.lookup (ofString b) = some (.val (.word B))) :
    evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address))
      [.op .sub [sszLocal a, sszLocal b], .const size, .const 9223372036854775807] =
      some [.val (.word (A - B)), .val (.word size), .val (.word 9223372036854775807)] := by
  simp [sszLocal, evalListHOLFinite, evalListHOLExact, evalHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord]

/-- One fixed-list-count declaration adds at most 67 ticks to its continuation. -/
theorem reqCount_bounded {σ : Type} (s : PanSemStateFiniteExact 64 σ) (n a b : String) (size : BitVec 64)
    (rest : ProgHOL 64) (A B : BitVec 64) (T : Nat)
    (ha : s.locals.lookup (ofString a) = some (.val (.word A)))
    (hb : s.locals.lookup (ofString b) = some (.val (.word B)))
    (code : s.code = originalRuntimeCode) (nz : size ≠ 0)
    (restBound : ReqBounded (fun t : PanSemStateFiniteExact 64 σ => t.code = originalRuntimeCode ∧
      ∀ k, k ≠ ofString n → t.locals.lookup k = s.locals.lookup k) rest T)
    (enough : 67 + T ≤ s.clock) :
    s.clock ≤ (evaluateHOLFiniteState s (reqCount n a b size rest)).2.clock + (67 + T) ∧
      (evaluateHOLFiniteState s (reqCount n a b size rest)).2.clock ≤ s.clock ∧
      (evaluateHOLFiniteState s (reqCount n a b size rest)).1 ≠ some .timeOut := by
  have args := reqCount_args s a b A B size ha hb
  have lookup := pan_three_word_shape_lookup s.code.lookup (ofString "ssz_fixed_list_count")
    (ofString "len") (ofString "sz") (ofString "lim") (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) .one
    (A - B) size 9223372036854775807 (by decide_cbv) (by decide_cbv) (by decide_cbv)
    (by rw [code]; exact originalRuntimeCode_sszFixedListCount_lookup)
  let entry := callEntryStateHOLFinite s (reqCountLocals (A - B) size)
  have el : entry.locals.lookup (ofString "len") = some (.val (.word (A - B))) := by
    simp [entry, reqCountLocals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "sz" ≠ ofString "len" by decide_cbv, show ofString "lim" ≠ ofString "len" by decide_cbv]
  have es : entry.locals.lookup (ofString "sz") = some (.val (.word size)) := by
    simp [entry, reqCountLocals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "lim" ≠ ofString "sz" by decide_cbv]
  have elim : entry.locals.lookup (ofString "lim") = some (.val (.word 9223372036854775807)) := by
    simp [entry, reqCountLocals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have body := evaluate_sszFixedListCount_body entry (A - B) size 9223372036854775807 code el es elim nz
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update
      (ofString "len",.val (.word (A - B)))).update (ofString "sz",.val (.word size))).update
      (ofString "lim",.val (.word 9223372036854775807)))) (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) with
  | mk result post =>
    have run' : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) = (result, post) := run
    rw [run'] at body metadata
    dsimp only at body metadata
    obtain ⟨b1, b2, b3, _, _⟩ := body
    have entryClock : entry.clock = s.clock - 1 := rfl
    rw [entryClock] at b1 b2 b3
    unfold reqCount
    have total := evaluate_decCall_checked_continuation_bounded s post (ofString n) (ofString "ssz_fixed_list_count")
      .one .one _ _ _ rest _ result 67 T args lookup (by omega) run (by change post.clock ≤ s.clock - 1; omega)
      (by omega) (b3 (by omega)) (by
        intro value _ _
        have postCode : post.code = originalRuntimeCode := metadata.1.trans code
        exact restBound _ ⟨postCode, fun k hk => by
          simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]⟩ (by
            change T ≤ post.clock; omega))
    exact total

#print axioms reqCount_bounded

theorem reqStores_straight : straightLine reqStores = true := by
  unfold reqStores reqStore; rfl

theorem reqStores_bounded {σ : Type} (P : PanSemStateFiniteExact 64 σ → Prop) : ReqBounded P reqStores 0 := by
  intro t _ _
  have clock := clockPreserving_of_straightLine reqStores reqStores_straight t
  exact ⟨by omega, by omega, evaluate_straightLine_no_timeout reqStores reqStores_straight t⟩

def ReqCountsPre {σ : Type} (t : PanSemStateFiniteExact 64 σ) : Prop :=
  t.code = originalRuntimeCode ∧ ∃ L O0 O1 O2 O3 O4 : BitVec 64,
    t.locals.lookup (ofString "len") = some (.val (.word L)) ∧
    t.locals.lookup (ofString "o0") = some (.val (.word O0)) ∧
    t.locals.lookup (ofString "o1") = some (.val (.word O1)) ∧
    t.locals.lookup (ofString "o2") = some (.val (.word O2)) ∧
    t.locals.lookup (ofString "o3") = some (.val (.word O3)) ∧
    t.locals.lookup (ofString "o4") = some (.val (.word O4))

/-- The five actual fixed-list-count declarations and the request stores. -/
theorem reqCounts_bounded {σ : Type} : ReqBounded (σ := σ) ReqCountsPre reqCounts 335 := by
  rintro t ⟨code, L, O0, O1, O2, O3, O4, hL, h0, h1, h2, h3, h4⟩ enough
  unfold reqCounts
  refine reqCount_bounded t "n0" "o1" "o0" 192 _ O1 O0 268 h1 h0 code (by decide) ?_ enough
  rintro t1 ⟨c1, k1⟩ en1
  refine reqCount_bounded t1 "n1" "o2" "o1" 76 _ O2 O1 201 ((k1 _ (by decide_cbv)).trans h2)
    ((k1 _ (by decide_cbv)).trans h1) c1 (by decide) ?_ en1
  rintro t2 ⟨c2, k2⟩ en2
  refine reqCount_bounded t2 "n2" "o3" "o2" 116 _ O3 O2 134 ((k2 _ (by decide_cbv)).trans ((k1 _ (by decide_cbv)).trans h3))
    ((k2 _ (by decide_cbv)).trans ((k1 _ (by decide_cbv)).trans h2)) c2 (by decide) ?_ en2
  rintro t3 ⟨c3, k3⟩ en3
  refine reqCount_bounded t3 "n3" "o4" "o3" 184 _ O4 O3 67
    ((k3 _ (by decide_cbv)).trans ((k2 _ (by decide_cbv)).trans ((k1 _ (by decide_cbv)).trans h4)))
    ((k3 _ (by decide_cbv)).trans ((k2 _ (by decide_cbv)).trans ((k1 _ (by decide_cbv)).trans h3))) c3 (by decide) ?_ en3
  rintro t4 ⟨c4, k4⟩ en4
  refine reqCount_bounded t4 "n4" "len" "o4" 68 _ L O4 0
    ((k4 _ (by decide_cbv)).trans ((k3 _ (by decide_cbv)).trans ((k2 _ (by decide_cbv)).trans ((k1 _ (by decide_cbv)).trans hL))))
    ((k4 _ (by decide_cbv)).trans ((k3 _ (by decide_cbv)).trans ((k2 _ (by decide_cbv)).trans ((k1 _ (by decide_cbv)).trans h4))))
    c4 (by decide) (reqStores_bounded _) en4

#print axioms reqCounts_bounded
end InitECandidate.Runtime
