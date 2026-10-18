import InitECandidate.Runtime.DecodeRequestsStoresReturned
import InitECandidate.Runtime.SszFixedListCountFrame
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Facts after a returned fixed-list-count declaration: exact division and a
continuation state with the caller's memory, globals, domain, code and other locals. -/
def ReqCountStep {σ : Type} (s : PanSemStateFiniteExact 64 σ) (n : String) (q : BitVec 64)
    (t : PanSemStateFiniteExact 64 σ) : Prop :=
  t.memory = s.memory ∧ t.globals = s.globals ∧ t.memaddrs = s.memaddrs ∧ t.code = s.code ∧
    (∀ k, k ≠ ofString n → t.locals.lookup k = s.locals.lookup k) ∧
    t.locals.lookup (ofString n) = some (.val (.word q))

theorem reqCount_returned {σ : Type} (s post : PanSemStateFiniteExact 64 σ) (n a b : String) (size : BitVec 64)
    (rest : ProgHOL 64) (A B : BitVec 64) (v : ValueHOL 64)
    (ha : s.locals.lookup (ofString a) = some (.val (.word A)))
    (hb : s.locals.lookup (ofString b) = some (.val (.word B)))
    (code : s.code = originalRuntimeCode) (nz : size ≠ 0)
    (run : evaluateHOLFiniteState s (reqCount n a b size rest) = (some (.returned v), post)) :
    (A - B) % size = 0 ∧ ∃ t output, ReqCountStep s n ((A - B) / size) t ∧
      evaluateHOLFiniteState t rest = (some (.returned v), output) ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  have args := reqCount_args s a b A B size ha hb
  have lookup := pan_three_word_shape_lookup s.code.lookup (ofString "ssz_fixed_list_count")
    (ofString "len") (ofString "sz") (ofString "lim") (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) .one
    (A - B) size 9223372036854775807 (by decide_cbv) (by decide_cbv) (by decide_cbv)
    (by rw [code]; exact originalRuntimeCode_sszFixedListCount_lookup)
  unfold reqCount at run
  obtain ⟨value, bodyPost, output, bodyRun, _, tail, postEq⟩ := evaluate_decCall_checked_returned_exact_scope s post
    (ofString n) (ofString "ssz_fixed_list_count") .one .one _ _ _ rest _ v args lookup run
  let entry := callEntryStateHOLFinite s (reqCountLocals (A - B) size)
  have el : entry.locals.lookup (ofString "len") = some (.val (.word (A - B))) := by
    simp [entry, reqCountLocals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "sz" ≠ ofString "len" by decide_cbv, show ofString "lim" ≠ ofString "len" by decide_cbv]
  have es : entry.locals.lookup (ofString "sz") = some (.val (.word size)) := by
    simp [entry, reqCountLocals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "lim" ≠ ofString "sz" by decide_cbv]
  have elim : entry.locals.lookup (ofString "lim") = some (.val (.word 9223372036854775807)) := by
    simp [entry, reqCountLocals, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have bodyRun' : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) =
      (some (.returned value), bodyPost) := bodyRun
  have body := evaluate_sszFixedListCount_body entry (A - B) size 9223372036854775807 code el es elim nz
  have frame := evaluate_sszFixedListCount_body_frame entry (A - B) size code el es nz
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)
  rw [bodyRun'] at body frame metadata
  dsimp only at body frame metadata
  obtain ⟨hv, hmod, _⟩ := body.2.2.2.2 value rfl
  obtain ⟨fm, fg⟩ := frame (Or.inr (Or.inr (Or.inr ⟨value, rfl⟩)))
  subst hv
  refine ⟨hmod, setVarHOLFinite (ofString n) (.val (.word ((A - B) / size))) {bodyPost with locals := s.locals}, output, ⟨fm, fg, metadata.2.1, metadata.1, fun k hk => ?_, ?_⟩, tail, ?_, ?_, ?_⟩
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  all_goals rw [postEq]

#print axioms reqCount_returned

/-- A returned run of the five count declarations and stores. -/
theorem reqCounts_returned {σ : Type} (s post : PanSemStateFiniteExact 64 σ) (rq p L O0 O1 O2 O3 O4 : BitVec 64)
    (v : ValueHOL 64) (code : s.code = originalRuntimeCode)
    (hrq : s.locals.lookup (ofString "rq") = some (.val (.word rq)))
    (hp : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (hL : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (h0 : s.locals.lookup (ofString "o0") = some (.val (.word O0)))
    (h1 : s.locals.lookup (ofString "o1") = some (.val (.word O1)))
    (h2 : s.locals.lookup (ofString "o2") = some (.val (.word O2)))
    (h3 : s.locals.lookup (ofString "o3") = some (.val (.word O3)))
    (h4 : s.locals.lookup (ofString "o4") = some (.val (.word O4)))
    (run : evaluateHOLFiniteState s reqCounts = (some (.returned v), post)) :
    (O1 - O0) % 192 = 0 ∧ (O2 - O1) % 76 = 0 ∧ (O3 - O2) % 116 = 0 ∧ (O4 - O3) % 184 = 0 ∧ (L - O4) % 68 = 0 ∧
      v = .val (.word rq) ∧
      (∀ x ∈ reqCellValues p O0 O1 O2 O3 O4 ((O1 - O0) / 192) ((O2 - O1) / 76) ((O3 - O2) / 116)
        ((O4 - O3) / 184) ((L - O4) / 68), s.memaddrs (rq + x.1)) ∧
      post.memory = memWrites s.memory rq (reqCellValues p O0 O1 O2 O3 O4 ((O1 - O0) / 192) ((O2 - O1) / 76)
        ((O3 - O2) / 116) ((O4 - O3) / 184) ((L - O4) / 68)) ∧
      post.globals = s.globals ∧ post.memaddrs = s.memaddrs := by
  unfold reqCounts at run
  obtain ⟨m0, t0, out0, st0, r0, pm0, pg0, pd0⟩ := reqCount_returned s post "n0" "o1" "o0" 192 _ O1 O0 v h1 h0 code (by decide) run
  have code0 : t0.code = originalRuntimeCode := st0.2.2.2.1.trans code
  obtain ⟨m1, t1, out1, st1, r1, pm1, pg1, pd1⟩ := reqCount_returned t0 out0 "n1" "o2" "o1" 76 _ O2 O1 v ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h2) ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h1) code0 (by decide) r0
  have code1 : t1.code = originalRuntimeCode := st1.2.2.2.1.trans code0
  obtain ⟨m2, t2, out2, st2, r2, pm2, pg2, pd2⟩ := reqCount_returned t1 out1 "n2" "o3" "o2" 116 _ O3 O2 v ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h3)) ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h2)) code1 (by decide) r1
  have code2 : t2.code = originalRuntimeCode := st2.2.2.2.1.trans code1
  obtain ⟨m3, t3, out3, st3, r3, pm3, pg3, pd3⟩ := reqCount_returned t2 out2 "n3" "o4" "o3" 184 _ O4 O3 v ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h4))) ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h3))) code2 (by decide) r2
  have code3 : t3.code = originalRuntimeCode := st3.2.2.2.1.trans code2
  obtain ⟨m4, t4, out4, st4, r4, pm4, pg4, pd4⟩ := reqCount_returned t3 out3 "n4" "len" "o4" 68 _ L O4 v ((st3.2.2.2.2.1 _ (by decide_cbv)).trans ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans hL)))) ((st3.2.2.2.2.1 _ (by decide_cbv)).trans ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h4)))) code3 (by decide) r3
  have code4 : t4.code = originalRuntimeCode := st4.2.2.2.1.trans code3
  obtain ⟨hv, dom, mem, glob, dd⟩ := reqStores_returned t4 out4 rq p O0 O1 O2 O3 O4 _ _ _ _ _ v ((st4.2.2.2.2.1 _ (by decide_cbv)).trans ((st3.2.2.2.2.1 _ (by decide_cbv)).trans ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans hrq))))) ((st4.2.2.2.2.1 _ (by decide_cbv)).trans ((st3.2.2.2.2.1 _ (by decide_cbv)).trans ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans hp))))) ((st4.2.2.2.2.1 _ (by decide_cbv)).trans ((st3.2.2.2.2.1 _ (by decide_cbv)).trans ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h0))))) ((st4.2.2.2.2.1 _ (by decide_cbv)).trans ((st3.2.2.2.2.1 _ (by decide_cbv)).trans ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h1))))) ((st4.2.2.2.2.1 _ (by decide_cbv)).trans ((st3.2.2.2.2.1 _ (by decide_cbv)).trans ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h2))))) ((st4.2.2.2.2.1 _ (by decide_cbv)).trans ((st3.2.2.2.2.1 _ (by decide_cbv)).trans ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h3))))) ((st4.2.2.2.2.1 _ (by decide_cbv)).trans ((st3.2.2.2.2.1 _ (by decide_cbv)).trans ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans ((st0.2.2.2.2.1 _ (by decide_cbv)).trans h4))))) ((st4.2.2.2.2.1 _ (by decide_cbv)).trans ((st3.2.2.2.2.1 _ (by decide_cbv)).trans ((st2.2.2.2.2.1 _ (by decide_cbv)).trans ((st1.2.2.2.2.1 _ (by decide_cbv)).trans st0.2.2.2.2.2)))) ((st4.2.2.2.2.1 _ (by decide_cbv)).trans ((st3.2.2.2.2.1 _ (by decide_cbv)).trans ((st2.2.2.2.2.1 _ (by decide_cbv)).trans st1.2.2.2.2.2))) ((st4.2.2.2.2.1 _ (by decide_cbv)).trans ((st3.2.2.2.2.1 _ (by decide_cbv)).trans st2.2.2.2.2.2)) ((st4.2.2.2.2.1 _ (by decide_cbv)).trans st3.2.2.2.2.2) st4.2.2.2.2.2 r4
  have tm : t4.memory = s.memory := st4.1.trans (st3.1.trans (st2.1.trans (st1.1.trans st0.1)))
  have tg : t4.globals = s.globals := st4.2.1.trans (st3.2.1.trans (st2.2.1.trans (st1.2.1.trans st0.2.1)))
  have td : t4.memaddrs = s.memaddrs := st4.2.2.1.trans (st3.2.2.1.trans (st2.2.2.1.trans (st1.2.2.1.trans st0.2.2.1)))
  refine ⟨m0, m1, m2, m3, m4, hv, fun x hx => td ▸ dom x hx, ?_, ?_, ?_⟩
  · rw [pm0, pm1, pm2, pm3, pm4, mem, tm]
  · rw [pg0, pg1, pg2, pg3, pg4, glob, tg]
  · rw [pd0, pd1, pd2, pd3, pd4, dd, td]

#print axioms reqCounts_returned
end InitECandidate.Runtime
