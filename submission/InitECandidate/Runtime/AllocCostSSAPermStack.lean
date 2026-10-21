import InitECandidate.Runtime.AllocCostSSATransport
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordSemStateFiniteExact Flapjack.WordProps
open InitECandidate.Runtime.WordToStack
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
theorem wordPathWork_permStack_variant {C F : Type} :
    ∀ (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
      (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame 64)),
      List.Forall₂ permStack xs s.stack →
      noAllocSubprogsHOL p = true → noInstallSubprogsHOL p = true →
      WordProps.noAllocCode s.code → WordProps.noInstallCode s.code →
      wordPathWork p ({ s with permute := k, stack := xs } :
        WordSemStateFiniteExact 64 C F) = wordPathWork p s
  | .seq first second, s, k, xs, hxs, hna, hni, hca, hci => by
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.and_eq_true] at hna hni
      obtain ⟨k1, xs1, he, hrel⟩ := swap_aux first s k xs hxs hna.1 hni.1 hca hci
      have hcode := code_evaluate first s hni.1 hci
      rcases h1 : evaluate first s with ⟨res, s1⟩
      rw [h1] at he hrel hcode
      have hcl := evaluate_clock first s res s1 h1
      exact wordPathWork_seq_variant first second s k xs res s1 k1 xs1 h1 he
        (wordPathWork_permStack_variant first s k xs hxs hna.1 hni.1 hca hci)
        (wordPathWork_permStack_variant second s1 k1 xs1 hrel hna.2 hni.2
          (hcode ▸ hca) (hcode ▸ hci))
  | .ite cmp reg operand first second, s, k, xs, hxs, hna, hni, hca, hci => by
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.and_eq_true] at hna hni
      exact wordPathWork_ite_variant cmp reg operand first second s k xs
        (wordPathWork_permStack_variant first s k xs hxs hna.1 hni.1 hca hci)
        (wordPathWork_permStack_variant second s k xs hxs hna.2 hni.2 hca hci)
  | .loop names body exitNames, s, k, xs, hxs, hna, hni, hca, hci => by
      have hna' := hna
      have hni' := hni
      simp only [noAllocSubprogsHOL, noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] at hna' hni'
      rcases hcs : cutState (names, .ln) s with _ | cs
      · have hT : cutState (names, .ln) ({ s with permute := k, stack := xs }) = none := by
          rw [cutState_swap, hcs]; rfl
        rw [wordPathWork_loop, wordPathWork_loop, hcs, hT]
      · obtain ⟨l, hl⟩ := cutStateConst (names, .ln) s cs hcs
        have hst : cs.stack = s.stack := by rw [hl]
        have hce : cs.code = s.code := by rw [hl]
        have hca' : WordProps.noAllocCode cs.code := by rw [hce]; exact hca
        have hci' : WordProps.noInstallCode cs.code := by rw [hce]; exact hci
        have hT : cutState (names, .ln) ({ s with permute := k, stack := xs }) =
            some ({ cs with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F) := by
          rw [cutState_swap, hcs]; rfl
        obtain ⟨k1, xs1, he, hrel⟩ := swap_aux body cs k xs (hst ▸ hxs) hna' hni' hca' hci'
        have hcode := code_evaluate body cs hni' hci'
        rcases hb : evaluate body cs with ⟨res, s1⟩
        rw [hb] at he hrel hcode
        have hcode' : s1.code = cs.code := hcode
        have hcl := evaluate_clock body cs res s1 hb
        have hc3 := cutState_clock_termdep (names, .ln) s cs hcs
        exact wordPathWork_loop_variant names body exitNames s k xs cs hcs hT res s1 k1 xs1
          hb he
          (wordPathWork_permStack_variant body cs k xs (hst ▸ hxs) hna' hni' hca' hci')
          (fun hz => wordPathWork_permStack_variant (.loop names body exitNames)
            (decClock s1) k1 xs1 hrel hna hni
            (by simp only [decClock]; rw [hcode']; exact hca')
            (by simp only [decClock]; rw [hcode']; exact hci'))
  | .mustTerminate q, s, k, xs, hxs, hna, hni, hca, hci =>
      wordPathWork_mustTerminate_variant q s k xs
  | .skip, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .move a b, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .inst a, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .assign a b, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .get a b, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .set a b, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .store a b, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .tick, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .storeConsts a b c d f, s, k, xs, hxs, hna, hni, hca, hci =>
      by rw [wordPathWork, wordPathWork]; all_goals simp
  | .return a b, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .break a, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .continue a, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .opCurrHeap a b c, s, k, xs, hxs, hna, hni, hca, hci =>
      by rw [wordPathWork, wordPathWork]; all_goals simp
  | .locValue a b, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .install a b c d f, s, k, xs, hxs, hna, hni, hca, hci =>
      by rw [wordPathWork, wordPathWork]; all_goals simp
  | .codeBufferWrite a b, s, k, xs, hxs, hna, hni, hca, hci =>
      by rw [wordPathWork, wordPathWork]; all_goals simp
  | .dataBufferWrite a b, s, k, xs, hxs, hna, hni, hca, hci =>
      by rw [wordPathWork, wordPathWork]; all_goals simp
  | .ffi a b c d f g, s, k, xs, hxs, hna, hni, hca, hci =>
      by rw [wordPathWork, wordPathWork]; all_goals simp
  | .shareInst a b c, s, k, xs, hxs, hna, hni, hca, hci =>
      by rw [wordPathWork, wordPathWork]; all_goals simp
  | .alloc a b, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .raise n, s, k, xs, hxs, hna, hni, hca, hci => by rw [wordPathWork, wordPathWork]; all_goals simp
  | .call ret dest args hdl, s, k, xs, hxs, hna, hni, hca, hci => by
      rcases hg : getVars args s with _ | xs0
      · rw [wordPathWork_call_getVars_none ret dest args hdl s hg,
            wordPathWork_call_getVars_none ret dest args hdl
              ({ s with permute := k, stack := xs }) (by rw [getVars_swap]; exact hg)]
      · by_cases hbad : wordSemBadDestArgs dest args = true
        · rw [wordPathWork_call_badDest ret dest args hdl s xs0 hg hbad,
              wordPathWork_call_badDest ret dest args hdl
                ({ s with permute := k, stack := xs }) xs0 (by rw [getVars_swap]; exact hg) hbad]
        · have hbad' : wordSemBadDestArgs dest args = false := by
            cases h : wordSemBadDestArgs dest args with
            | false => rfl
            | true => exact absurd h hbad
          rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs0) s.code s.stackSize with
            _ | ⟨args1, prog, ss⟩
          · rw [wordPathWork_call_findCode_none ret dest args hdl s xs0 hg hbad' hf,
                wordPathWork_call_findCode_none ret dest args hdl
                  ({ s with permute := k, stack := xs }) xs0 (by rw [getVars_swap]; exact hg) hbad' hf]
          · have hpa := WordProps.noAllocFindCode s.code dest _ _ _ prog _ ⟨hf, hca⟩
            have hpi := WordProps.noInstallFindCode s.code dest _ _ _ prog _ ⟨hci, hf⟩
            have hdec : decClock ({ s with permute := k, stack := xs }) = ({ decClock s with permute := k, stack := xs } :
                WordSemStateFiniteExact 64 C F) := rfl
            rcases ret with _ | rv
            ·
              rcases hdl with _ | hv
              ·
                by_cases hz : s.clock = 0
                · rw [wordPathWork_call_none_clock_zero dest args s hg hbad' hf hz,
                      wordPathWork_call_none_clock_zero dest args ({ s with permute := k, stack := xs })
                        (by rw [getVars_swap]; exact hg) hbad' hf hz]
                · rw [wordPathWork_call_none_body_eq dest args s xs0 args1 prog ss
                      hg hbad' hf hz,
                    wordPathWork_call_none_body_eq dest args ({ s with permute := k, stack := xs }) xs0 args1 prog ss
                      (by rw [getVars_swap]; exact hg) hbad' hf hz]
                  rw [hdec, callEnv_swap (decClock s) k xs hxs]
                  rw [wordPathWork_permStack_variant prog
                    (callEnv args1 ss (decClock s)) k xs hxs hpa hpi hca hci]
              ·
                rw [wordPathWork_call_none_handler dest args hv s hg hbad' hf,
                    wordPathWork_call_none_handler dest args hv ({ s with permute := k, stack := xs })
                      (by rw [getVars_swap]; exact hg) hbad' hf]
            ·
              obtain ⟨values, names, retCode, l1, l2⟩ := rv
              by_cases hdc : sptDomainEmpty names.1 ∨ ¬ values.Nodup
              · rw [wordPathWork_call_returning_dom values names retCode l1 l2 dest args
                    hdl s xs0 args1 prog ss hg hbad' hf hdc,
                  wordPathWork_call_returning_dom values names retCode l1 l2 dest args
                    hdl ({ s with permute := k, stack := xs }) xs0 args1 prog ss
                    (by rw [getVars_swap]; exact hg) hbad' hf hdc]
              · obtain ⟨hdom, hnodup⟩ := by simpa only [not_or, not_not] using hdc
                rcases hce : wordSemCutEnvs names s.locals with _ | envs
                · rw [wordPathWork_call_returning_cut_none values names retCode l1 l2 dest
                      args hdl s xs0 args1 prog ss hg hbad' hf hdom hnodup hce,
                    wordPathWork_call_returning_cut_none values names retCode l1 l2 dest
                      args hdl ({ s with permute := k, stack := xs }) xs0 args1 prog ss
                      (by rw [getVars_swap]; exact hg) hbad' hf hdom hnodup hce]
                · by_cases hz : s.clock = 0
                  · rw [wordPathWork_call_returning_clock_zero values names retCode l1 l2
                        dest args hdl s xs0 envs args1 prog ss hg hbad' hf hdom hnodup
                        hce hz,
                      wordPathWork_call_returning_clock_zero values names retCode l1 l2
                        dest args hdl ({ s with permute := k, stack := xs }) xs0 envs args1 prog ss
                        (by rw [getVars_swap]; exact hg) hbad' hf hdom hnodup hce hz]
                  · obtain ⟨k1, xs1, hpe, hrel1⟩ := pushEnv_swap (decClock s) k xs hxs envs hdl
                    have hcpre : (callEnv args1 ss (pushEnv envs hdl (decClock s))).code =
                        s.code := code_pushEnv envs hdl _
                    obtain ⟨k2, xs2, he, hrel2⟩ := swap_aux prog
                      (callEnv args1 ss (pushEnv envs hdl (decClock s))) k1 xs1 hrel1
                      hpa hpi (hcpre ▸ hca) (hcpre ▸ hci)
                    have hcode := code_evaluate prog _ hpi (hcpre ▸ hci)
                    have hentry : callEnv args1 ss (pushEnv envs hdl (decClock ({ s with permute := k, stack := xs }))) =
                        ({ callEnv args1 ss (pushEnv envs hdl (decClock s)) with
                          permute := k1, stack := xs1 } : WordSemStateFiniteExact 64 C F) := by
                      rw [hdec, hpe, callEnv_swap _ k1 xs1 hrel1]
                    have ihBody : wordPathWork prog (callEnv args1 ss (pushEnv envs hdl
                        (decClock ({ s with permute := k, stack := xs })))) =
                        wordPathWork prog (callEnv args1 ss (pushEnv envs hdl (decClock s))) := by
                      rw [hentry]
                      exact wordPathWork_permStack_variant prog
                        (callEnv args1 ss (pushEnv envs hdl (decClock s))) k1 xs1 hrel1
                        hpa hpi (hcpre ▸ hca) (hcpre ▸ hci)
                    rcases hb : evaluate prog
                      (callEnv args1 ss (pushEnv envs hdl (decClock s))) with ⟨rc, s2⟩
                    rw [hb] at he hrel2 hcode
                    have hc := evaluate_clock prog _ rc s2 hb
                    have h2 : s2.code = s.code := hcode.trans hcpre
                    rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | bl | cl | _ | _ | f1 | _
                    · rw [wordPathWork_call_returning_other_variant values names retCode l1 l2
                          dest args hdl s k xs xs0 args1 prog ss envs none s2
                          ({ s2 with permute := k2, stack := xs2 }) hg hbad' hf hdom hnodup hce hz
                          hb (by simp) (by simp) (by rw [hentry]; exact he) ihBody]
                    · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ values.length
                      · rw [wordPathWork_call_returning_result_fall values names retCode l1 l2
                            dest args hdl ({ s with permute := k, stack := xs }) ({ s2 with permute := k2, stack := xs2 })
                            xs0 envs args1 prog ss x ys (by rw [getVars_swap]; exact hg) hbad'
                            hf hdom hnodup hce hz
                            (by rw [hentry, fix_clock_evaluate]; exact he) hx,
                          wordPathWork_call_returning_result_fall values names retCode l1 l2
                            dest args hdl s s2 xs0 envs args1 prog ss x ys hg hbad' hf
                            hdom hnodup hce hz (by rw [fix_clock_evaluate, hb]) hx]
                        rw [ihBody]
                      · have hxl : x = WordLocW.loc l1 l2 := by
                          by_contra h; exact hx (Or.inl h)
                        have hyl : ys.length = values.length := by
                          by_contra h; exact hx (Or.inr h)
                        have hp := popEnv_swap s2 k2 xs2 hrel2
                        rcases hpop : popEnv s2 with _ | s1
                        · rw [wordPathWork_call_returning_result_pop_none values names retCode
                              l1 l2 dest args hdl ({ s with permute := k, stack := xs })
                              ({ s2 with permute := k2, stack := xs2 }) xs0 envs args1 prog ss x ys
                              (by rw [getVars_swap]; exact hg) hbad' hf hdom hnodup hce hz
                              (by rw [hentry, fix_clock_evaluate]; exact he)
                              (hp.1 hpop) hxl hyl,
                            wordPathWork_call_returning_result_pop_none values names retCode
                              l1 l2 dest args hdl s s2 xs0 envs args1 prog ss x ys
                              hg hbad' hf hdom hnodup hce hz
                              (by rw [fix_clock_evaluate, hb]) hpop hxl hyl]
                          rw [ihBody]
                        · obtain ⟨xs3, hpe3, hrel3⟩ := hp.2 s1 hpop
                          have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
                            ⟨popEnv_clock _ _ hpop, popEnv_termdep _ _ hpop⟩
                          have h3 : s1.code = s.code :=
                            ((popEnvConst _ _ hpop).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).trans h2
                          by_cases hdu : sptDomainEqUnion s1.locals envs.1 envs.2
                          · have ihRet : wordPathWork retCode ({ setVars values ys s1 with
                                permute := k2, stack := xs3 } :
                                WordSemStateFiniteExact 64 C F) =
                                wordPathWork retCode (setVars values ys s1) :=
                              wordPathWork_permStack_variant retCode (setVars values ys s1)
                                k2 xs3 hrel3 (noAlloc_call_ret hna) (noInstall_call_ret hni)
                                (h3 ▸ hca) (h3 ▸ hci)
                            rw [wordPathWork_call_returning_result_variant values names retCode
                              l1 l2 dest args hdl s k xs xs0 args1 prog ss envs x ys s2
                              ({ s2 with permute := k2, stack := xs2 }) s1 k2 xs3 hg hbad' hf
                              hdom hnodup hce hz hb hpop hxl hyl hdu
                              (by rw [hentry]; exact he) hpe3 ihBody ihRet]
                          · rw [wordPathWork_call_returning_result_union_false values names
                                retCode l1 l2 dest args hdl ({ s with permute := k, stack := xs })
                                ({ s2 with permute := k2, stack := xs2 })
                                ({ s1 with permute := k2, stack := xs3 }) xs0 envs args1 prog ss
                                x ys (by rw [getVars_swap]; exact hg) hbad' hf hdom hnodup hce hz
                                (by rw [hentry, fix_clock_evaluate]; exact he) hpe3 hxl hyl hdu,
                              wordPathWork_call_returning_result_union_false values names
                                retCode l1 l2 dest args hdl s s2 s1 xs0 envs args1 prog ss
                                x ys hg hbad' hf hdom hnodup hce hz
                                (by rw [fix_clock_evaluate, hb]) hpop hxl hyl hdu]
                            rw [ihBody]
                    · rcases hdl with _ | hv
                      ·
                        rw [wordPathWork_call_returning_exception_unhandled values names
                              retCode l1 l2 dest args none ({ s with permute := k, stack := xs })
                              ({ s2 with permute := k2, stack := xs2 }) xs0 envs args1 prog ss x y
                              (by rw [getVars_swap]; exact hg) hbad' hf hdom hnodup hce hz
                              (by rw [hentry, fix_clock_evaluate]; exact he) rfl,
                            wordPathWork_call_returning_exception_unhandled values names
                              retCode l1 l2 dest args none s s2 xs0 envs args1 prog ss x y
                              hg hbad' hf hdom hnodup hce hz
                              (by rw [fix_clock_evaluate, hb]) rfl]
                        rw [ihBody]
                      ·
                        obtain ⟨reg, hprog, hl1, hl2⟩ := hv
                        by_cases hd : x = WordLocW.loc hl1 hl2
                        · by_cases hdu2 : sptDomainEqUnion s2.locals envs.1 envs.2
                          · have ihHandler : wordPathWork hprog ({ setVar reg y s2 with
                                permute := k2, stack := xs2 } :
                                WordSemStateFiniteExact 64 C F) =
                                wordPathWork hprog (setVar reg y s2) :=
                              wordPathWork_permStack_variant hprog (setVar reg y s2) k2 xs2
                                hrel2 (noAlloc_call_handler hna) (noInstall_call_handler hni)
                                (h2 ▸ hca) (h2 ▸ hci)
                            rw [wordPathWork_call_returning_exception_variant values names
                              retCode l1 l2 dest args (some (reg, hprog, hl1, hl2)) s k xs xs0 args1 prog ss envs x y
                              s2 k2 xs2 reg hprog hl1 hl2 hg hbad'
                              hf hdom hnodup hce hz hb rfl hd hdu2 (by rw [hentry]; exact he)
                              ihBody ihHandler]
                          · rw [wordPathWork_call_returning_exception_union_false values names
                                retCode l1 l2 dest args (some (reg, hprog, hl1, hl2)) ({ s with permute := k, stack := xs })
                                ({ s2 with permute := k2, stack := xs2 }) xs0 envs args1 prog ss
                                x y reg hprog hl1 hl2 (by rw [getVars_swap]; exact hg) hbad' hf
                                hdom hnodup hce hz
                                (by rw [hentry, fix_clock_evaluate]; exact he) rfl hd hdu2,
                              wordPathWork_call_returning_exception_union_false values names
                                retCode l1 l2 dest args (some (reg, hprog, hl1, hl2)) s s2 xs0 envs args1 prog ss x y
                                reg hprog hl1 hl2 hg hbad' hf hdom hnodup hce hz
                                (by rw [fix_clock_evaluate, hb]) rfl hd hdu2]
                            rw [ihBody]
                        · rw [wordPathWork_call_returning_exception_fall values names retCode
                              l1 l2 dest args (some (reg, hprog, hl1, hl2)) ({ s with permute := k, stack := xs })
                              ({ s2 with permute := k2, stack := xs2 }) xs0 envs args1 prog ss x y
                              reg hprog hl1 hl2 (by rw [getVars_swap]; exact hg) hbad' hf hdom
                              hnodup hce hz (by rw [hentry, fix_clock_evaluate]; exact he)
                              rfl hd,
                            wordPathWork_call_returning_exception_fall values names retCode
                              l1 l2 dest args (some (reg, hprog, hl1, hl2)) s s2 xs0 envs args1 prog ss x y reg hprog
                              hl1 hl2 hg hbad' hf hdom hnodup hce hz
                              (by rw [fix_clock_evaluate, hb]) rfl hd]
                          rw [ihBody]
                    · exact wordPathWork_call_returning_other_variant values names retCode l1 l2
                          dest args hdl s k xs xs0 args1 prog ss envs (some (.break bl)) s2
                          ({ s2 with permute := k2, stack := xs2 }) hg hbad' hf hdom hnodup hce hz
                          hb (by simp) (by simp) (by rw [hentry]; exact he) ihBody
                    · exact wordPathWork_call_returning_other_variant values names retCode l1 l2
                          dest args hdl s k xs xs0 args1 prog ss envs (some (.continue cl)) s2
                          ({ s2 with permute := k2, stack := xs2 }) hg hbad' hf hdom hnodup hce hz
                          hb (by simp) (by simp) (by rw [hentry]; exact he) ihBody
                    · exact wordPathWork_call_returning_other_variant values names retCode l1 l2
                          dest args hdl s k xs xs0 args1 prog ss envs (some .timeOut) s2
                          ({ s2 with permute := k2, stack := xs2 }) hg hbad' hf hdom hnodup hce hz
                          hb (by simp) (by simp) (by rw [hentry]; exact he) ihBody
                    · exact wordPathWork_call_returning_other_variant values names retCode l1 l2
                          dest args hdl s k xs xs0 args1 prog ss envs
                          (some .notEnoughSpace) s2
                          ({ s2 with permute := k2, stack := xs2 }) hg hbad' hf hdom hnodup hce hz
                          hb (by simp) (by simp) (by rw [hentry]; exact he) ihBody
                    · exact wordPathWork_call_returning_other_variant values names retCode l1 l2
                          dest args hdl s k xs xs0 args1 prog ss envs (some (.finalFfi f1)) s2
                          ({ s2 with permute := k2, stack := xs2 }) hg hbad' hf hdom hnodup hce hz
                          hb (by simp) (by simp) (by rw [hentry]; exact he) ihBody
                    · exact wordPathWork_call_returning_other_variant values names retCode l1 l2
                          dest args hdl s k xs xs0 args1 prog ss envs (some .error) s2
                          ({ s2 with permute := k2, stack := xs2 }) hg hbad' hf hdom hnodup hce hz
                          hb (by simp) (by simp) (by rw [hentry]; exact he) ihBody
termination_by p s => (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (rcases hc with ⟨_, _⟩)
    try (rcases hcl with ⟨_, _⟩)
    try (rcases hc2 with ⟨_, _⟩)
    try (rcases hc3 with ⟨_, _⟩)
    try simp +zetaDelta only [Flapjack.WordSemStateFiniteExact.decClock,
      Flapjack.WordSemStateFiniteExact.callEnv, Flapjack.WordSemStateFiniteExact.setVars,
      Flapjack.WordSemStateFiniteExact.setVar, pushEnv_clock, pushEnv_termdep, true_and] at *
    first
    | omega
    | (left; omega)
    | (right; refine ⟨by omega, Or.inl (by omega)⟩)
    | (right; refine ⟨by omega, Or.inr ⟨by omega, by decreasing_tactic⟩⟩)

#print axioms wordPathWork_permStack_variant

end InitECandidate.Runtime.FineCost
