import InitECandidate.Runtime.PtRestGD
import InitECandidate.Runtime.PtSufEOGD
import InitECandidate.Runtime.PtOutGD
/-!
PtRestGD with the interpreter output record pointer `out = Y` threaded (`LPSo`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section lw
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB : BitVec 64} {Y : BitVec 64}

end lw

section rel
variable {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64} {Y : BitVec 64}

variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop} {Y : BitVec 64}

end rel

section pz
variable {D : BitVec 64 → Prop} {B : Bool}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {Hb Nj Hg : BitVec 64} {M0 : Mem} {Y : BitVec 64}

end pz

section cl
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd kA kB k16 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs Lo Hg : BitVec 64} {M0 : Mem} {Y : BitVec 64}

/-- Locals of the deletion loop: `LPSo Y` and a word index `i`. -/
def LDlO (Y : BitVec 64) (Ix : BitVec 64) (L : GA) : Prop :=
  LPSo Y Ix L ∧ ∃ Iv : BitVec 64, L.lookup (ofString "i") = some (.val (.word Iv))

/-- `del = lds(out + 24); if del != 0 { dcap = lds(del + 24); i = 0; while i < dcap { s = htab_item(del, i);
if s.0 != 0 { clear_account_preserving_balance(s.1) }; i = i + 1 } }; rest`: the deletion table and its count are
interpreter data (read only, any value); every deletion is a registry writer. -/
theorem ptRest_delO {QM : Mem → GA → Prop} {R : Mem → GA → Prop} (Ix : BitVec 64) {rest : ProgHOL 64}
    (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x)
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x) (hP0Lo : P0.toNat ≤ Lo.toNat)
    (ECH : BitVec 64) (hECH : G0.lookup (ofString "empty_code_hash") = some (.val (.word ECH)))
    (hR : ∀ (M M' : Mem) (G G' : GA) (H H' : BitVec 64), R M G → HeapIs G H → HeapIs G' H' →
      H.toNat ≤ H'.toNat → (∀ x, OutX Out Lo Hg x → ¬ InJ J C x → ¬ SkWin SKB x → M' x = M x) → R M' G')
    (hrest : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LPSo Y Ix L ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G) (fun _ M G => QM M G) RR rest) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => (LPSo Y Ix L ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G) (fun _ M G => QM M G) RR
      (.dec (ofString "del") .one (.load .one (.op .add [.var .local (ofString "out"),.const 24#64]))
        (.seq (.ite (.cmp .notEqual (.var .local (ofString "del")) (.const 0#64))
            (.dec (ofString "dcap") .one (.load .one (.op .add [.var .local (ofString "del"),.const 24#64]))
              (.seq (.assign .local (ofString "i") (.const 0#64))
                (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "dcap")))
                  (.decCall (ofString "s") (.comb [.one,.one,.one]) (ofString "htab_item")
                    [.var .local (ofString "del"),.var .local (ofString "i")]
                    (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "s"))) (.const 0#64))
                        (.call (some (none,none)) (ofString "clear_account_preserving_balance")
                          [.rfield 1 (.var .local (ofString "s"))]) .skip)
                      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64])))))))
            .skip)
          rest)) := by
  refine aqgd_decD (Qb := fun _ M G => QM M G) (ofString "del") .one _ (fun h => h.elim)
    (Pb := fun L M G => (LPSo Y Ix L ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G)
    (fun s v _ _ _ _ ⟨⟨lp,pz⟩,r⟩ _ _ _ => ⟨⟨lpso_upd lp _ v (by decide) (by decide),pz⟩,r⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
    (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) hrest
  refine aqgd_conseq (P := fun L M G => (LPSo Y Ix L ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G) ?_
    (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_decD (Qb := fun L M G => (LPSo Y Ix L ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G) (ofString "dcap")
    .one _ (fun h => h.elim) (Pb := fun L M G => (LPSo Y Ix L ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G)
    (fun s v _ _ _ _ ⟨⟨lp,pz⟩,r⟩ _ _ _ => ⟨⟨lpso_upd lp _ v (by decide) (by decide),pz⟩,r⟩) ?_
    (fun _ _ _ _ _ _ _ ⟨⟨lp,pz⟩,r⟩ => ⟨⟨lpso_res lp _ _ (by decide) (by decide),pz⟩,r⟩)
  refine aqgd_seq (aqgd_assignLocal (Q := fun L M G => (LDlO Y Ix L ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G) _ _
    (fun s v _ _ ⟨⟨lp,pz⟩,r⟩ _ ev => by
      simp [EV,evalHOLExact] at ev; subst ev
      exact ⟨⟨⟨lpso_upd lp _ _ (by decide) (by decide),0#64,lookup_update_eq' _ _ _⟩,pz⟩,r⟩)) ?_
  refine aqgd_conseq (aqgd_whileI _ ?_) (fun _ _ _ h => h) (fun _ _ _ ⟨⟨⟨lp,_⟩,pz⟩,r⟩ => ⟨⟨lp,pz⟩,r⟩)
    (fun _ _ _ h => h)
  -- s = htab_item(del, i): read-only
  refine aqgd_decCallSpecF
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => ((LDlO Y Ix L ∧ ∃ a b d : BitVec 64,
      L.lookup (ofString "s") = some (.rStruct [.val (.word a),.val (.word b),.val (.word d)])) ∧
      PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G)
    (Qc := fun L M G => (LDlO Y Ix L ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G)
    _ _ _ _ _ _ _ originalRuntimeCode_htabItem_lookup
    (fun _ M0' G0' _ => aqgd_of_mf htabItem_memoryFrame (by body_check Guest.guestFn_htab_item)
      (by body_check Guest.guestFn_htab_item) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ ?_
    (fun _ _ _ _ _ _ _ ⟨⟨⟨lp,Iv,hi⟩,pz⟩,r⟩ => ⟨⟨⟨lpso_res lp _ _ (by decide) (by decide),Iv,
      by rw [resVarEq_lookup_ne' _ _ _ _ (by decide)]; exact hi⟩,pz⟩,r⟩)
  · intro L M G v M' G' ⟨⟨⟨⟨lp,Iv,hi⟩,pz⟩,r⟩,_⟩ ⟨e1,e2⟩ ok
    subst e1 e2
    obtain ⟨a,b,d,rfl⟩ := triple_of_shape ok
    exact ⟨⟨⟨⟨lpso_upd lp _ _ (by decide) (by decide),Iv,by rw [lookup_update_ne' _ _ (by decide)]; exact hi⟩,
      a,b,d,lookup_update_eq' _ _ _⟩,pz⟩,r⟩
  refine aqgd_seq (Q := fun L M G => ((LDlO Y Ix L ∧ ∃ a b d : BitVec 64,
      L.lookup (ofString "s") = some (.rStruct [.val (.word a),.val (.word b),.val (.word d)])) ∧
      PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_conseq (aqgd_call_clearAcct_pz _ ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 jfit hwJ hwP hOut hwS
          hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hWsP0 hJE hSE hP0Lo ECH hECH (fun s lp v ev => ?_) hR)
        (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  · obtain ⟨_,a,b,d,hs⟩ := lp
    simp [EV,evalHOLExact,hs] at ev
    exact ⟨b,ev.symm⟩
  · exact aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨⟨lp,Iv,hi⟩,_⟩,pz⟩,r⟩ _ ev => by
      simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
      subst ev
      exact ⟨⟨⟨lpso_upd lp _ _ (by decide) (by decide),Iv + 1#64,lookup_update_eq' _ _ _⟩,pz⟩,r⟩)

#print axioms ptRest_delO
/-- `tx_frame_mark = lds(out + 80); if tx_frame_mark != 0 { scratch_release(tx_frame_mark);
frame_mem_release(lds(out + 88)) }; return 0`. -/
theorem ptRest_tailO {R : Mem → GA → Prop} (Ix Y : BitVec 64)
    (hRu : ∀ M G (gname : MlS) (y : BitVec 64), (gname = ofString "scratch_ptr" ∨ gname = ofString "frame_mem_ptr") →
      R M G → R M (G.update (gname,.val (.word y))))
    (hRet : ∀ L M G, (LPSo Y Ix L ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G → RR (.val (.word 0#64)) M G) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => ((LPSo Y Ix L ∧ L.lookup (ofString "out") = some (.val (.word Y))) ∧
        PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧ R M G ∧ OutRec SP0 FM Y M) (fun _ _ _ => False) RR
      (.dec (ofString "tx_frame_mark") .one (.load .one (.op .add [.var .local (ofString "out"),.const 80#64]))
        (.seq (.ite (.cmp .notEqual (.var .local (ofString "tx_frame_mark")) (.const 0#64))
            (.seq (.call (some (none,none)) (ofString "scratch_release") [.var .local (ofString "tx_frame_mark")])
              (.call (some (none,none)) (ofString "frame_mem_release")
                [.load .one (.op .add [.var .local (ofString "out"),.const 88#64])]))
            .skip)
          (.return (.const 0#64)))) := by
  refine aqgd_decD (Qb := fun _ _ _ => False) (ofString "tx_frame_mark") .one _ (fun h => h.elim)
    (Pb := fun L M G => ∃ Tm : BitVec 64, ((((LPSo Y Ix L ∧ L.lookup (ofString "out") = some (.val (.word Y))) ∧
      L.lookup (ofString "tx_frame_mark") = some (.val (.word Tm))) ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧
      R M G) ∧ (Tm = 0#64 ∨ (FM.toNat ≤ Tm.toNat ∧ Tm.toNat ≤ SP0.toNat ∧ M (Y + 88#64) = .word FM))) ?_ ?_
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v _ _ _ _ ⟨⟨⟨lp,ho⟩,pz⟩,r,orc⟩ _ ev _
    rw [ev_load_off s _ Y 80#64 v ho ev]
    rcases orc with h0 | ⟨m,hm,lo,hi,h88⟩
    · rw [h0]
      exact ⟨0#64,⟨⟨⟨⟨lpso_upd lp _ _ (by decide) (by decide),by rw [lookup_update_ne' _ _ (by decide)]; exact ho⟩,
        lookup_update_eq' _ _ _⟩,pz⟩,r⟩,Or.inl rfl⟩
    · rw [hm]
      exact ⟨m,⟨⟨⟨⟨lpso_upd lp _ _ (by decide) (by decide),by rw [lookup_update_ne' _ _ (by decide)]; exact ho⟩,
        lookup_update_eq' _ _ _⟩,pz⟩,r⟩,Or.inr ⟨lo,hi,h88⟩⟩
  refine aqgd_exE (fun Tm => ?_)
  refine aqgd_seq (Q := fun L M G => ((((LPSo Y Ix L ∧ L.lookup (ofString "out") = some (.val (.word Y))) ∧
      L.lookup (ofString "tx_frame_mark") = some (.val (.word Tm))) ∧ PZ n c T Out ko D B Excl Lo Hg M0 M G) ∧
      R M G)) ?_ (aqgd_return _ (fun s v G _ hG ⟨⟨⟨⟨lp,_⟩,_⟩,pz⟩,r⟩ _ ev => by
        unfold GIs at hG; subst hG
        simp [EV,evalHOLExact] at ev; subst ev
        exact hRet _ _ _ ⟨⟨lp,pz⟩,r⟩))
  refine aqgd_iteD (CT := fun _ _ _ => Tm ≠ 0#64) (CF := fun _ _ _ => True) _ ?_ ?_
    (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
  · intro F s x _ _ _ _ ⟨⟨⟨⟨_,ht⟩,_⟩,_⟩,_⟩ _ ev
    simp [EV,evalHOLExact,ht] at ev
    simp only [Compiler.Encoders.Asm.wordCmpHOL] at ev
    by_cases e : Tm = 0#64
    · subst e; simp at ev; subst ev; exact ⟨fun h => absurd rfl h,fun _ => trivial⟩
    · simp [e] at ev; subst ev; exact ⟨fun _ => e,fun _ => trivial⟩
  refine aqgd_conseq (P := fun L M G => ((((LPSo Y Ix L ∧ L.lookup (ofString "out") = some (.val (.word Y))) ∧
      L.lookup (ofString "tx_frame_mark") = some (.val (.word Tm))) ∧
      ((PZ n c T Out ko D B Excl Lo Hg M0 M G ∧ R M G) ∧ M (Y + 88#64) = .word FM)) ∧
      (FM.toNat ≤ Tm.toNat ∧ Tm.toNat ≤ SP0.toNat)))
    (Q := fun L M G => (((LPSo Y Ix L ∧ L.lookup (ofString "out") = some (.val (.word Y))) ∧
      L.lookup (ofString "tx_frame_mark") = some (.val (.word Tm))) ∧
      ((PZ n c T Out ko D B Excl Lo Hg M0 M G ∧ R M G) ∧ M (Y + 88#64) = .word FM)))
    (aqgd_pureE (fun ⟨lo,hi⟩ => ?_))
    (fun L M G ⟨⟨⟨⟨lp,pz⟩,r⟩,dj⟩,ne⟩ => by
      rcases dj.resolve_left ne with ⟨lo,hi,h88⟩
      exact ⟨⟨lp,⟨pz,r⟩,h88⟩,lo,hi⟩)
    (fun L M G ⟨lp,⟨pz,r⟩,_⟩ => ⟨⟨lp,pz⟩,r⟩) (fun _ _ _ h => h)
  have hRu' : ∀ (gname : MlS) (y : BitVec 64), (gname = ofString "scratch_ptr" ∨ gname = ofString "frame_mem_ptr") →
      ∀ (L : GA) (M : Mem) (G : GA), ((LPSo Y Ix L ∧ L.lookup (ofString "out") = some (.val (.word Y))) ∧
        L.lookup (ofString "tx_frame_mark") = some (.val (.word Tm))) →
      ((PZ n c T Out ko D B Excl Lo Hg M0 M G ∧ R M G) ∧ M (Y + 88#64) = .word FM) →
      ((PZ n c T Out ko D B Excl Lo Hg M0 M (G.update (gname,.val (.word y))) ∧
        R M (G.update (gname,.val (.word y)))) ∧ M (Y + 88#64) = .word FM) := by
    intro gname y hg L M G _ ⟨⟨pz,r⟩,h88⟩
    refine ⟨⟨pz_gupd pz _ _ ?_ ?_,hRu M G gname y hg r⟩,h88⟩ <;> rcases hg with rfl | rfl <;> decide
  refine aqgd_seq (aqgd_call_gsetter (ofString "scratch_release") (ofString "scratch_ptr") _ Tm
    (by rw [originalRuntimeCode_scratchRelease_lookup,srcScratchRelease_eq])
    (fun g h => jwsbus_setScratch h Tm lo hi) (fun s lp _ v ev => by simp [EV,evalHOLExact,lp.2] at ev; exact ev.symm)
    (hRu' _ _ (Or.inl rfl))) ?_
  exact aqgd_call_gsetter (ofString "frame_mem_release") (ofString "frame_mem_ptr") _ FM
    (by rw [originalRuntimeCode_frameMemRelease_lookup,source_frameMemRelease_body])
    (fun g h => jwsbus_setFrame h)
    (fun s lp r v ev => by rw [ev_load_off s _ Y 88#64 v lp.1.2 ev,r.2])
    (hRu' _ _ (Or.inr rfl))

#print axioms ptRest_tailO
end cl
end InitECandidate.Runtime
