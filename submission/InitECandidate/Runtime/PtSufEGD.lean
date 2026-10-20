import InitECandidate.Runtime.PtSufDGD
import InitECandidate.Runtime.PtSufCGD
/-!
Spine drop 126 of the actual `process_transaction` from the prefix state `PXR` (with the transaction's `Excl`): the
suffix phase fixes `Hb` (the heap pointer at the drop, at least `P0`) and moves to `PB` with `Excl'`, which extends
`Excl` by the block-list words. The two block lists `lds(bo + 40)`, `lds(bo + 72)` are valid at transaction entry
(header words outside words not in `Excl`, so the prefix kept them; header and buffer words among the disjoint sets
`W40`, `W72` of block-object words for `Excl'`; buffers of `8·cap` bytes below `P0`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section e
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl Excl' : BitVec 64 → Prop} {J C SKB Bo U Sc H0 : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}

/-- Precondition strengthening using the arena predicate. -/
theorem aqgd_conseqA {A : GA → Prop} {Vn : MlS → Prop} {P P' Q : GA → Mem → GA → Prop} {p : ProgHOL 64}
    (h : AQGD D B A w Vn P' Q RR p) (hp : ∀ L M g, A g → P L M g → P' L M g) : AQGD D B A w Vn P Q RR p := by
  intro F s code dom aw sl H hH pre
  unfold GIs at hH; subst hH
  exact h F s code dom aw sl _ rfl (hp _ _ _ aw pre)

/-- A list valid at transaction entry (header kept since) is a block list in the suffix state. -/
def BL0 (Wb Excl : BitVec 64 → Prop) (Out : BitVec 64 → Prop) (P0 Lh : BitVec 64) (M0 : Mem) : Prop :=
  (∀ x, HdW Lh x → Out x ∧ ¬ Excl x ∧ Wb x) ∧ Lh.toNat + 24 ≤ P0.toNat ∧
    ∃ P N Cp : BitVec 64, LHd Lh P N Cp M0 ∧ N.toNat ≤ Cp.toNat ∧ 0 < Cp.toNat ∧ P.toNat + 8 * Cp.toNat ≤ P0.toNat ∧
      ∀ x : BitVec 64, P.toNat ≤ x.toNat → x.toNat < P.toNat + 8 * Cp.toNat → Wb x ∧ ¬ HdW Lh x

theorem bl_of_bl0 {Wb : BitVec 64 → Prop} {Lh Hb : BitVec 64} {M : Mem} {G : GA} (h : BL0 Wb Excl Out P0 Lh M0)
    (fr : ∀ x, Out x → ¬ Excl x → M x = M0 x) (hH : HeapIs G Hb) (hP0 : P0.toNat ≤ Hb.toNat) :
    BL Wb Hb Lh 8#64 M G := by
  obtain ⟨hW,hL,P,N,Cp,⟨d0,d8,d16⟩,hNC,hC0,hbuf,inW⟩ := h
  have k : ∀ x, HdW Lh x → M x = M0 x := fun x hx => fr x (hW x hx).1 (hW x hx).2.1
  have e8 : (8#64).toNat = 8 := rfl
  exact ⟨fun x hx => (hW x hx).2.2,by omega,P,N,Cp,Hb,⟨(k _ (Or.inl rfl)).trans d0,
    (k _ (Or.inr (Or.inl rfl))).trans d8,(k _ (Or.inr (Or.inr rfl))).trans d16⟩,hH,hNC,hC0,by rw [e8]; omega,
    Or.inl (fun x lo hi => inW x lo (by rw [e8] at hi; exact hi))⟩

/-- Spine drop 126 of `process_transaction` for any continuation `rest` (from `del = lds(out + 24)` on). -/
theorem ptSufD_126 {QM : Mem → GA → Prop} (Ix L40 L72 : BitVec 64) {rest : ProgHOL 64}
    (hsub : ∀ x, Excl x → Excl' x)
    (hW40 : ∀ x, W40 x → BW n c Out Excl' w x) (hW72 : ∀ x, W72 x → BW n c Out Excl' w x)
    (hdis : ∀ x, W40 x → ¬ W72 x) (hOut : Out w)
    (hB40 : Out (Bo + 40#64) ∧ ¬ Excl' (Bo + 40#64) ∧ M0 (Bo + 40#64) = .word L40)
    (hB72 : Out (Bo + 72#64) ∧ ¬ Excl' (Bo + 72#64) ∧ M0 (Bo + 72#64) = .word L72)
    (hL40 : BL0 W40 Excl Out P0 L40 M0) (hL72 : BL0 W72 Excl Out P0 L72 M0)
    (hrest : ∀ Hb Nj Nl Lp : BitVec 64, H0.toNat ≤ Hb.toNat →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => (LDn Ix Nl Lp L ∧ PB n c T Out ko D B Excl' Hb Nj M0 M G) ∧
          BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) (fun _ M G => QM M G) RR rest) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (.dec (ofString "nl") .one (.load .one (.op .add [.var .local (ofString "logs"),.const 8#64]))
        (.dec (ofString "lp") .one (.load .one (.op .add [.var .local (ofString "logs"),.const 0#64]))
          (.seq (.assign .local (ofString "i") (.const 0#64))
            (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
                (.decCall (ofString "slot") .one (ofString "lst_push")
                  [.load .one (.op .add [.var .global (ofString "bo"),.const 40#64]),.const 8#64]
                  (.seq (.store (.var .local (ofString "slot"))
                      (.load .one (.op .add [.var .local (ofString "lp"),
                        .panop .mul [.var .local (ofString "i"),.const 8#64]])))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64])))))
              (.dec (ofString "stable_log_cap") .one (.var .local (ofString "nl"))
                (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0#64))
                    (.assign .local (ofString "stable_log_cap") (.const 1#64)) .skip)
                  (.decCall (ofString "stable_logs") .one (ofString "lst_new")
                    [.const 8#64,.var .local (ofString "stable_log_cap")]
                    (.seq (.store (.op .add [.var .local (ofString "stable_logs"),.const 8#64])
                        (.var .local (ofString "nl")))
                      (.dec (ofString "stable_lp") .one
                        (.load .one (.op .add [.var .local (ofString "stable_logs"),.const 0#64]))
                        (.seq (.assign .local (ofString "i") (.const 0#64))
                          (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
                              (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
                                  .panop .mul [.var .local (ofString "i"),.const 8#64]])
                                (.load .one (.op .add [.var .local (ofString "lp"),
                                  .panop .mul [.var .local (ofString "i"),.const 8#64]])))
                                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64]))))
                            (.decCall (ofString "rl") .one (ofString "lst_push")
                              [.load .one (.op .add [.var .global (ofString "bo"),.const 72#64]),.const 8#64]
                              (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs")))
                                rest))))))))))))) := by
  refine aqgd_conseqA (P' := fun L M G => ∃ Hb Nj : BitVec 64, ((LPS Ix L ∧ PB n c T Out ko D B Excl' Hb Nj M0 M G) ∧
      BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) ∧ H0.toNat ≤ Hb.toNat) ?_ ?_
  · exact aqgd_exE (fun Hb => aqgd_exE (fun Nj => aqgd_pureE (fun h0 =>
      ptSufD_head Ix L40 L72 hW40 hW72 hdis (fun x hx => (hL40.1 x hx).2.2) (fun x hx => (hL72.1 x hx).2.2) hOut
        hB40 hB72 (fun Nl Lp => hrest Hb Nj Nl Lp h0))))
  · intro L M g aw ⟨lp,px⟩
    obtain ⟨Hb,Nj,hH,h0,pb⟩ := pb_of_pxr px
    have hP0 := (jws_heap_facts aw.1.1.1 hH).1
    exact ⟨Hb,Nj,⟨⟨lp,pb_excl pb hsub⟩,bl_of_bl0 hL40 pb.2.2.2 hH hP0,bl_of_bl0 hL72 pb.2.2.2 hH hP0⟩,h0⟩

#print axioms ptSufD_126
end e

/-- The actual `process_transaction` from `del = lds(out + 24)` on: the deletion loop over `del` with
`clear_account_preserving_balance`, `incorporate_tx_into_block()`, the frame release, and `return 0`. -/
def ptRest134 : ProgHOL 64 :=
  .dec (ofString "del") .one (.load .one (.op .add [.var .local (ofString "out"),.const 24#64]))
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
      (.seq (.call (some (none,none)) (ofString "incorporate_tx_into_block") [])
        (.dec (ofString "tx_frame_mark") .one (.load .one (.op .add [.var .local (ofString "out"),.const 80#64]))
          (.seq (.ite (.cmp .notEqual (.var .local (ofString "tx_frame_mark")) (.const 0#64))
              (.seq (.call (some (none,none)) (ofString "scratch_release") [.var .local (ofString "tx_frame_mark")])
                (.call (some (none,none)) (ofString "frame_mem_release")
                  [.load .one (.op .add [.var .local (ofString "out"),.const 88#64])]))
              .skip)
            (.return (.const 0#64))))))

/-- Spine drop 126 of the actual `process_transaction` is the log-copy segment followed by `ptRest134`. -/
theorem processTx_drop126_eq :
    stateInitSpineDrop 126 (sourceFunctionBody Guest.guestFn_process_transaction) =
      .dec (ofString "nl") .one (.load .one (.op .add [.var .local (ofString "logs"),.const 8#64]))
        (.dec (ofString "lp") .one (.load .one (.op .add [.var .local (ofString "logs"),.const 0#64]))
          (.seq (.assign .local (ofString "i") (.const 0#64))
            (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
                (.decCall (ofString "slot") .one (ofString "lst_push")
                  [.load .one (.op .add [.var .global (ofString "bo"),.const 40#64]),.const 8#64]
                  (.seq (.store (.var .local (ofString "slot"))
                      (.load .one (.op .add [.var .local (ofString "lp"),
                        .panop .mul [.var .local (ofString "i"),.const 8#64]])))
                    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64])))))
              (.dec (ofString "stable_log_cap") .one (.var .local (ofString "nl"))
                (.seq (.ite (.cmp .equal (.var .local (ofString "stable_log_cap")) (.const 0#64))
                    (.assign .local (ofString "stable_log_cap") (.const 1#64)) .skip)
                  (.decCall (ofString "stable_logs") .one (ofString "lst_new")
                    [.const 8#64,.var .local (ofString "stable_log_cap")]
                    (.seq (.store (.op .add [.var .local (ofString "stable_logs"),.const 8#64])
                        (.var .local (ofString "nl")))
                      (.dec (ofString "stable_lp") .one
                        (.load .one (.op .add [.var .local (ofString "stable_logs"),.const 0#64]))
                        (.seq (.assign .local (ofString "i") (.const 0#64))
                          (.seq (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "nl")))
                              (.seq (.store (.op .add [.var .local (ofString "stable_lp"),
                                  .panop .mul [.var .local (ofString "i"),.const 8#64]])
                                (.load .one (.op .add [.var .local (ofString "lp"),
                                  .panop .mul [.var .local (ofString "i"),.const 8#64]])))
                                (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64]))))
                            (.decCall (ofString "rl") .one (ofString "lst_push")
                              [.load .one (.op .add [.var .global (ofString "bo"),.const 72#64]),.const 8#64]
                              (.seq (.store (.var .local (ofString "rl")) (.var .local (ofString "stable_logs")))
                                ptRest134)))))))))))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_process_transaction,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,stateInitSpineDrop]
  rfl

#print axioms processTx_drop126_eq

section c1
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB k40 : Fin n}
  {Excl Excl' : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem} {W40 W72 : BitVec 64 → Prop}

/-- The actual `process_transaction` body from spine drop 1 through the block-list pushes: every callee discharged
except the interpreter entry `process_message_call` (explicit `PmcC`); the suffix from `del = lds(out + 24)` on
(`ptRest134`) explicit, in the suffix state `PB` with `Excl'` and both block lists valid. -/
theorem processTx_to_delS {QM : Mem → GA → Prop} (Ix Arr Rarr L40 L72 : BitVec 64)
    (pc : PmcC SP0 P0 FM G0 J C SKB Bo U Sc w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_process_message_call))
    {DF : Nat} (hF : Fence D DF) (hDF : DF + 9 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (hSc0 : Sc ≠ 0)
    (hwSc : ¬ MWin Sc 448 w) (hScE : ∀ x, MWin Sc 448 x → Excl x)
    (scSafe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → ¬ MWin Sc 448 x)
    (hkoSc : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → ¬ MWin Sc 448 x)
    (hBoD : D (Bo + 24)) (hBoO : Out (Bo + 24)) (hBoE : ¬ Excl (Bo + 24)) (hArr : M0 (Bo + 24) = .word Arr)
    (hO0 : Out (Arr + Ix * 16) ∧ ∀ i, Arr + Ix * 16 ≠ c i) (hE0 : Excl (Arr + Ix * 16)) (hw0 : w ≠ Arr + Ix * 16)
    (hO8 : Out (Arr + Ix * 16 + 8) ∧ ∀ i, Arr + Ix * 16 + 8 ≠ c i) (hE8 : Excl (Arr + Ix * 16 + 8))
    (hw8 : w ≠ Arr + Ix * 16 + 8)
    (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (hc16 : c k16 = Ts + 16#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
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
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x)
    (ne40 : k40 ≠ ko) (hc40 : c k40 = Ts + 40#64)
    (hU : U.toNat + 640 ≤ 2 ^ 64) (hwWS : ¬ WS U w) (hWO : ∀ x, WS U x → Out x ∧ ∀ i, x ≠ c i)
    (hWE : ∀ x, WS U x → Excl x)
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x)
    (hBoC : ∀ k : BitVec 64, k = 0#64 ∨ k = 8#64 ∨ k = 16#64 ∨ k = 48#64 →
      (Out (Bo + k) ∧ ∀ i, Bo + k ≠ c i) ∧ Excl (Bo + k) ∧ w ≠ Bo + k)
    (hR32D : D (Bo + 32)) (hR32O : Out (Bo + 32)) (hR32E : ¬ Excl (Bo + 32)) (hRarr : M0 (Bo + 32) = .word Rarr)
    (hRO0 : Out (Rarr + Ix * 16) ∧ ∀ i, Rarr + Ix * 16 ≠ c i) (hRE0 : Excl (Rarr + Ix * 16))
    (hRw0 : w ≠ Rarr + Ix * 16)
    (hRO8 : Out (Rarr + Ix * 16 + 8) ∧ ∀ i, Rarr + Ix * 16 + 8 ≠ c i) (hRE8 : Excl (Rarr + Ix * 16 + 8))
    (hRw8 : w ≠ Rarr + Ix * 16 + 8)
    (hsub : ∀ x, Excl x → Excl' x)
    (hW40 : ∀ x, W40 x → BW n c Out Excl' w x) (hW72 : ∀ x, W72 x → BW n c Out Excl' w x)
    (hdis : ∀ x, W40 x → ¬ W72 x)
    (hB40 : Out (Bo + 40#64) ∧ ¬ Excl' (Bo + 40#64) ∧ M0 (Bo + 40#64) = .word L40)
    (hB72 : Out (Bo + 72#64) ∧ ¬ Excl' (Bo + 72#64) ∧ M0 (Bo + 72#64) = .word L72)
    (hL40 : BL0 W40 Excl Out P0 L40 M0) (hL72 : BL0 W72 Excl Out P0 L72 M0)
    (hrest : ∀ Hb Nj Nl Lp : BitVec 64, H0.toNat ≤ Hb.toNat →
      AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
        (fun L M G => (LDn Ix Nl Lp L ∧ PB n c T Out ko D B Excl' Hb Nj M0 M G) ∧
          BL W40 Hb L40 8#64 M G ∧ BL W72 Hb L72 8#64 M G) (fun _ M G => QM M G) RR ptRest134) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_process_transaction)) :=
  processTx_to_126S Ix Arr Rarr pc hF hDF hcap hSc0 hwSc hScE scSafe hkoSc hBoD hBoO hBoE hArr hO0 hE0 hw0 hO8 hE8
    hw8 ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0
    safe hOutSafe hkoWs hJE hSE ne40 hc40 hU hwWS hWO hWE hWsP0 hBoC hR32D hR32O hR32E hRarr hRO0 hRE0 hRw0 hRO8
    hRE8 hRw8 (by
      rw [processTx_drop126_eq]
      exact ptSufD_126 Ix L40 L72 hsub hW40 hW72 hdis hOut hB40 hB72 hL40 hL72 hrest)

#print axioms processTx_to_delS
end c1
end InitECandidate.Runtime
