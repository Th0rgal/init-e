import InitECandidate.Runtime.PtSegFinGD
/-!
The actual `process_transaction` body from `te = te_new()` (spine drop 34) to the `process_message_call(m)` site
(spine drop 98): from `LPS` and `PXR` it reaches the `process_message_call` continuation with `LPS` and `PXR`, every
callee on the way discharged (`te_new`, `tx_has_access_list`, `alloc` with unchecked decoded sizes, fenced
access-list loops, `memcpy`, `tx_is_blob`, `tx_is_setcode`, `keccak256`, `msg_new`, `htab_new`, `htab_set`,
`get_account`, `compute_contract_address`). The continuation from drop 98 is the explicit premise `hpmc`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section all
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {DF : Nat}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem}

theorem processTx_teNew_to_pmc {QM : Mem → GA → Prop} (Ix : BitVec 64) (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62)
    (hcap : 33806089496 ≤ DF) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x) (hOut : Out w)
    (hpmc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 98 (sourceFunctionBody Guest.guestFn_process_transaction))) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 34 (sourceFunctionBody Guest.guestFn_process_transaction)) := by
  have hwP := (hOutSafe w hOut).2
  unfold sourceFunctionBody at hpmc ⊢
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq] at hpmc ⊢
  simp only [Guest.guestFn_process_transaction,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,stateInitSpineDrop] at hpmc ⊢
  have conv : ∀ L M G, LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G →
      ∃ S Lo Nj : BitVec 64, ((LK [(ofString "index",Ix),(ofString "sender",S)] L ∧
        SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ HeapIs G Lo) ∧
        (H0.toNat ≤ Lo.toNat ∧ ∀ i, (c i).toNat < Lo.toNat) := by
    intro L M G ⟨⟨hi,S,hs⟩,H,Nj,hH,h0,reg,hn,fr⟩
    refine ⟨S,H,Nj,⟨⟨fun p hp => ?_,⟨H,hH,le_refl _⟩,reg,hn,fr⟩,hH⟩,h0,fun i => ?_⟩
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl
      · exact hi
      · exact hs
    · obtain ⟨l,pure,_,_,_⟩ := reg
      exact regPure_below pure (c i) ⟨i,Or.inl rfl⟩
  refine aqgd_conseq (P := fun L M G => ∃ S Lo Nj : BitVec 64, ((LK [(ofString "index",Ix),(ofString "sender",S)] L ∧
      SI n c T Out ko D B Excl Lo Nj M0 M G) ∧ HeapIs G Lo) ∧ (H0.toNat ≤ Lo.toNat ∧ ∀ i, (c i).toNat < Lo.toNat))
    ?_ conv (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine aqgd_exE (fun S => aqgd_exE (fun Lo => aqgd_exE (fun Nj => aqgd_pureE (fun ⟨h0,hcLo⟩ => ?_))))
  refine aqgd_of_arenaFact (Φ := P0.toNat ≤ Lo.toNat ∧ Lo.toNat % 8 = 0)
    (fun _ _ g aw ⟨_,hH⟩ => let f := jws_heap_facts aw.1.1.1 hH; ⟨f.1,f.2.2⟩) ?_
  intro ⟨hP0Lo,hLo8⟩
  have hw : w.toNat < Lo.toNat := by omega
  refine aqgd_conseq (P := fun L M G => LK [(ofString "index",Ix),(ofString "sender",S)] L ∧
    SI n c T Out ko D B Excl Lo Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)
  refine ptSegTe hF hDF hw Ix S ?_
  refine ptSegAl hF hDF hcap hw Ix S ?_
  refine ptSegKeys hF hDF hcap hLo8 hw Ix S ?_
  refine ptSegTxh hF hDF K Pd NB hK0 hPd0 safe hOutSafe hkoWs hOut hLo8 hw Ix S ?_
  refine ptSegMsg hF hDF hw Ix S (fun Mm Taa Tak hLoM hMT hLoT _ => ?_)
  exact ptSegFin hF hDF hcap hAB hAo hBo hTs hBs hcA hcB K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hWsP0 hOut
    Ix S Lo Mm Taa Tak hP0Lo h0 hcLo hLoM hMT hLoT hpmc

#print axioms processTx_teNew_to_pmc
end all

section top
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB k40 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo U Sc Ts Bs H0 : BitVec 64} {M0 : Mem}

/-- The actual `process_transaction` body from `bal_index = index + 1` (spine drop 1) to the `process_message_call`
site (spine drop 98) over the scratch-pinned arena: every callee discharged; the continuation from drop 98 is the
explicit premise `hpmc`. -/
theorem processTx_to_pmcS {QM : Mem → GA → Prop} (Ix Arr : BitVec 64)
    {DF : Nat} (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (hSc0 : Sc ≠ 0)
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
    -- the workspace (frame stack, Keccak buffers, nibble scratch) lies below the heap floor `P0`
    (hWsP0 : ∀ x : BitVec 64, P0.toNat ≤ x.toNat → WsSafe SP0 FM K Pd NB x)
    (hpmc : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 98 (sourceFunctionBody Guest.guestFn_process_transaction))) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w (fun _ => False)
      (fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_process_transaction)) :=
  processTx_to_teNew_finalS Ix Arr hF hDF hcap hSc0 hwSc hScE scSafe hkoSc hBoD hBoO hBoE hArr hO0 hE0 hw0 hO8 hE8
    hw8 ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0
    safe hOutSafe hkoWs hJE hSE ne40 hc40 hU hwWS hWO hWE
    (processTx_teNew_to_pmc Ix hF hDF hcap hAB hAo hBo hTs hBs hcA hcB K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs
      hWsP0 hOut hpmc)

#print axioms processTx_to_pmcS
end top
end InitECandidate.Runtime
