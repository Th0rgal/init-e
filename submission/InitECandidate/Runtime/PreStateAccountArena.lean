import InitECandidate.Runtime.HtabSetArena
import InitECandidate.Runtime.OriginalPreStateAccountCode
import InitECandidate.Runtime.OriginalPreReadCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → Prop}

theorem set_aqm_ex (T : BitVec 64) (E : BitVec 64 → Prop) (KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat)
    (lay : HLay P0 T E KL SD C N KS VS US OS OPS b) (M0 : Mem) (hw : ¬ Foot P0 T E w) :
    AQM SP0 P0 FM G0 w (fun _ => True)
      (fun L M => (∃ Kk V : BitVec 64, LK (irP0 T Kk V) L) ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0)
      (fun _ _ => True) (fun _ M' => ∀ x, ¬ Foot P0 T E x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_htab_set) := by
  intro F s code dom aw sl ⟨⟨Kk,V,hl⟩,hh,hm⟩
  exact set_aqm T Kk V E KL SD C N KS VS US OS OPS b lay M0 hw F s code dom aw sl ⟨hl,hh,hm⟩

/-- `htab_set(lds (g + off), a2, a3)` on a table whose pointer lives in a static global's record. -/
theorem aqm_setCall {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} (g : MlS) (hg : g ∈ staticGlobalNames)
    (Gv off : BitVec 64) (hG0 : G0.lookup g = some (.val (.word Gv))) (a2 a3 : ExpHOL 64)
    (T : BitVec 64) (E : BitVec 64 → Prop) (KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat) (lay : HLay P0 T E KL SD C N KS VS US OS OPS b)
    (hw : ¬ Foot P0 T E w)
    (hP : ∀ L M, P L M → M (Gv + off) = .word T ∧ Hdr M T KL SD C N KS VS US OS OPS)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, P s.locals s.memory → SL Vn s.locals →
      (EV s a2 = some x ∨ EV s a3 = some x) → ∃ y : BitVec 64, x = .val (.word y))
    (hq : ∀ L M M', P L M → (∀ x, ¬ Foot P0 T E x → M' x = M x) → Q L M') :
    AQM SP0 P0 FM G0 w Vn P Q RR
      (.call (some (none,none)) (ofString "htab_set") [.load .one (.op .add [.var .global g,.const off]),a2,a3]) := by
  refine aqm_callSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' L M => (∃ Kk V : BitVec 64, LK (irP0 T Kk V) L) ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0')
    (RRe := fun _ M0' _ M' => ∀ x, ¬ Foot P0 T E x → M' x = M0' x)
    _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp)
    (fun _ M0' _ => set_aqm_ex T E KL SD C N KS VS US OS OPS b lay M0' hw) ?_ (fun L M v M' h h' => hq L M M' h h')
  intro F s values callee rs aw pre sl args lookup
  obtain ⟨hcell,hh⟩ := hP _ _ pre
  obtain ⟨eg,_⟩ := aw.2.2.2 g hg
  rw [evalListHOLFinite_eq_toExact] at args
  cases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.load .one (.op .add [.var .global g,.const off])) with
  | none => simp [evalListHOLExact,h1] at args
  | some x1 =>
    have e1 : x1 = .val (.word T) := by
      simp [evalHOLExact,evalListHOLExact,eg,hG0,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,hcell] at h1
      exact h1.2.symm
    subst e1
    cases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a2 with
    | none => simp [evalListHOLExact,h1,h2] at args
    | some x2 =>
      cases h3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a3 with
      | none => simp [evalListHOLExact,h1,h2,h3] at args
      | some x3 =>
        obtain ⟨y2,rfl⟩ := hargs s x2 pre sl (Or.inl h2)
        obtain ⟨y3,rfl⟩ := hargs s x3 pre sl (Or.inr h3)
        simp [evalListHOLExact,h1,h2,h3] at args
        subst args
        rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
          originalRuntimeCode_hashSet_lookup] at lookup
        simp only [Option.some.injEq,Prod.mk.injEq] at lookup
        obtain ⟨_,rfl,_⟩ := lookup
        refine ⟨⟨y2,y3,fun p hp => ?_⟩,hh,rfl⟩
        simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]

/-- An arena triple with trivial pre/post gives a memory-aware triple with trivial assertions. -/
theorem aqm_of_aq {p : ProgHOL 64} {Q' : HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    (h : AQ SP0 P0 FM G0 w Vn (fun _ => True) Q' p) :
    AQM SP0 P0 FM G0 w Vn (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) p := by
  intro F s code dom aw sl _
  obtain ⟨m,a,n,c,b⟩ := h F s code dom aw sl trivial
  exact ⟨m,a,fun e => ⟨(n e).1,trivial⟩,fun _ _ => trivial,c,b⟩

theorem source_recordPreRead_body : sourceFunctionBody Guest.guestFn_record_pre_state_read =
    .seq (.call (some (none,none)) (ofString "htab_set")
      [.load .one (.op .add [.var .global (ofString "bs"),.const 72]),.var .local (ofString "addr"),.const 1])
      (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- `record_pre_state_read(addr)`: the pre-state read table is updated through `htab_set` under its real layout. -/
theorem recordPreRead_aqm (Bv : BitVec 64) (hG0 : G0.lookup (ofString "bs") = some (.val (.word Bv)))
    (T : BitVec 64) (E : BitVec 64 → Prop) (KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat) (lay : HLay P0 T E KL SD C N KS VS US OS OPS b)
    (M0 : Mem) (hw : ¬ Foot P0 T E w) :
    AQM SP0 P0 FM G0 w (fun _ => True)
      (fun _ M => M (Bv + 72) = .word T ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0)
      (fun _ _ => True) (fun _ M' => ∀ x, ¬ Foot P0 T E x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_record_pre_state_read) := by
  rw [source_recordPreRead_body]
  refine aqm_seq (Q := fun _ M => ∀ x, ¬ Foot P0 T E x → M x = M0 x)
    (aqm_setCall (ofString "bs") (by decide) Bv 72 hG0 _ _ T E KL SD C N KS VS US OS OPS b lay hw
      (fun L M h => ⟨h.1,h.2.1⟩) ?_ ?_) (aqm_return _ (fun _ _ _ h _ _ => h))
  · intro F s x _ sl hx
    rcases hx with hx | hx
    · simp [EV,evalHOLExact] at hx
      exact sl _ trivial x hx
    · simp [EV,evalHOLExact] at hx
      exact ⟨1,hx.symm⟩
  · intro L M M' ⟨_,_,hm⟩ h x hx
    rw [← hm]; exact h x hx

/-- Facts at `get_pre_state_account_optional` entry: an account address, the transaction read table (pointer at
`ts + 8`) and the block pre-state read table (pointer at `bs + 72`) with their real layouts in memory. -/
def PreStateP (Ts Bs Ta KLa SDa Ca Na KSa VSa USa OSa OPSa Tb KLb SDb Cb Nb KSb VSb USb OSb OPSb : BitVec 64)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : Mem) : Prop :=
  (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
    M (Ts + 8) = .word Ta ∧ Hdr M Ta KLa SDa Ca Na KSa VSa USa OSa OPSa ∧
    M (Bs + 72) = .word Tb ∧ Hdr M Tb KLb SDb Cb Nb KSb VSb USb OSb OPSb

/-- After the transaction read is recorded: the block pre-state read table is still in memory. -/
def PreStateB (Bs Tb KLb SDb Cb Nb KSb VSb USb OSb OPSb : BitVec 64)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : Mem) : Prop :=
  (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
    M (Bs + 72) = .word Tb ∧ Hdr M Tb KLb SDb Cb Nb KSb VSb USb OSb OPSb

set_option maxHeartbeats 4000000 in
/-- `get_pre_state_account_optional` keeps the watched word in every outcome (traps, MPT/RLP errors, table growth
failures) and keeps the arena globals on continuing outcomes, when the watched word lies outside both read tables'
footprints, below `P0`, outside the scratch arena and the Keccak/nibble buffers; the block table's pointer cell and
header lie outside the transaction table's footprint. -/
theorem preState_aqm (Ts Bs : BitVec 64) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (Ta : BitVec 64) (Ea : BitVec 64 → Prop) (KLa SDa Ca Na KSa VSa USa OSa OPSa : BitVec 64) (ba : Nat)
    (layA : HLay P0 Ta Ea KLa SDa Ca Na KSa VSa USa OSa OPSa ba)
    (Tb : BitVec 64) (Eb : BitVec 64 → Prop) (KLb SDb Cb Nb KSb VSb USb OSb OPSb : BitVec 64) (bb : Nat)
    (layB : HLay P0 Tb Eb KLb SDb Cb Nb KSb VSb USb OSb OPSb bb)
    (sepB : ∀ x : BitVec 64, (x = Bs + 72 ∨ (Tb.toNat ≤ x.toNat ∧ x.toNat < Tb.toNat + 72)) → ¬ Foot P0 Ta Ea x)
    (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w)
    (oN : ∀ j : Nat, j < 64 → w ≠ panByteAlignHOL (NB + BitVec.ofNat 64 j))
    (hsc : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) (hp : w.toNat < P0.toNat)
    (hwA : ¬ Foot P0 Ta Ea w) (hwB : ¬ Foot P0 Tb Eb w) :
    AQM SP0 P0 FM G0 w (fun x => x ≠ ofString "w")
      (PreStateP Ts Bs Ta KLa SDa Ca Na KSa VSa USa OSa OPSa Tb KLb SDb Cb Nb KSb VSb USb OSb OPSb)
      (fun _ _ => True) (fun _ _ => True)
      (sourceFunctionBody Guest.guestFn_get_pre_state_account_optional) := by
  have fitB : Tb.toNat + 72 < 2 ^ 64 := by have := layB.hdr; have := layB.eEnd; omega
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_get_pre_state_account_optional,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  -- record the transaction read
  refine aqm_seq (Q := PreStateB Bs Tb KLb SDb Cb Nb KSb VSb USb OSb OPSb)
    (aqm_setCall (ofString "ts") (by decide) Ts 8 hTs _ _ Ta Ea KLa SDa Ca Na KSa VSa USa OSa OPSa ba layA hwA
      (fun L M h => ⟨h.2.1,h.2.2.1⟩) ?_ ?_) ?_
  · intro F s x ⟨⟨A,hA⟩,_⟩ _ hx
    rcases hx with hx | hx
    · simp [EV,evalHOLExact,hA] at hx; exact ⟨A,hx.symm⟩
    · simp [EV,evalHOLExact] at hx; exact ⟨1,hx.symm⟩
  · intro L M M' ⟨ha,_,_,hcell,hh⟩ h
    refine ⟨ha,(h _ (sepB _ (Or.inl rfl))).trans hcell,hdr_keep hh fitB (fun x lo hi => h x (sepB x (Or.inr ⟨lo,hi⟩)))⟩
  -- w = htab_get(lds (bs + 16), addr): read-only
  refine aqm_decCallSpec (Vn' := fun _ => False) (Pe := fun _ M0' _ M => M = M0') (RRe := fun _ M0' _ M' => M' = M0')
    (Pc := PreStateB Bs Tb KLb SDb Cb Nb KSb VSb USb OSb OPSb) (Qc := fun _ _ => True)
    _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp)
    (fun _ M0' _ => aqm_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) (fun _ _ _ hm _ _ _ => hm))
    (fun _ _ _ _ _ _ _ _ _ => rfl) (fun h => absurd rfl h) ?_ ?_ (fun _ _ _ _ _ _ => trivial)
  · intro L M v M' ⟨⟨A,hA⟩,hc,hh⟩ eM _
    subst eM
    exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,hc,hh⟩
  -- early return of a block-written account
  refine aqm_seq (Q := PreStateB Bs Tb KLb SDb Cb Nb KSb VSb USb OSb OPSb) (aqm_ite (CT := fun _ _ => True)
    (CF := fun _ _ => True) _ (fun _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
    (aqm_return _ (fun _ _ _ _ _ _ => trivial)) (aqm_conseq aqm_skip (fun _ _ h => h.1) (fun _ _ h => h)
      (fun _ _ h => h))) ?_
  -- record the block pre-state read
  refine aqm_seq (Q := fun L _ => ∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A)))
    (aqm_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' _ M => M (Bs + 72) = .word Tb ∧ Hdr M Tb KLb SDb Cb Nb KSb VSb USb OSb OPSb ∧ M = M0')
      (RRe := fun _ _ _ _ => True)
      _ _ _ _ _ originalRuntimeCode_recordPreStateRead_lookup (by simp)
      (fun _ M0' _ => aqm_conseq (recordPreRead_aqm Bs hBs Tb Eb KLb SDb Cb Nb KSb VSb USb OSb OPSb bb layB M0' hwB)
        (fun _ _ h => h) (fun _ _ h => h) (fun _ _ _ => trivial)) ?_ (fun _ _ _ _ h _ => h.1)) ?_
  · intro F s values callee rs _ ⟨⟨A,hA⟩,hc,hh⟩ _ _ _
    exact ⟨hc,hh,rfl⟩
  -- a = ws_get_account_optional(addr); return a
  refine aqm_decCallSpec (Vn' := fun x => x ≠ ofString "leaf") (Pe := fun _ _ _ _ => True) (RRe := fun _ _ _ _ => True)
    (Pc := fun _ _ => True) (Qc := fun _ _ => True) _ _ _ _ _ _ _ originalRuntimeCode_wsGetAccount_lookup (by simp)
    (fun _ _ _ => aqm_of_aq (wsGetAccount_aq K Pd NB hsc hp hK0 hPd0 hNB0 oK oP oN))
    (fun _ _ _ _ _ _ _ _ _ => trivial) (fun _ => rfl) (fun _ _ _ _ _ _ _ => trivial)
    (aqm_return _ (fun _ _ _ _ _ _ => trivial)) (fun _ _ _ _ _ _ => trivial)

/-- Frame form: `get_pre_state_account_optional` from any arena state whose memory carries both read tables. -/
theorem preState_frame (Ts Bs : BitVec 64) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (Ta : BitVec 64) (Ea : BitVec 64 → Prop) (KLa SDa Ca Na KSa VSa USa OSa OPSa : BitVec 64) (ba : Nat)
    (layA : HLay P0 Ta Ea KLa SDa Ca Na KSa VSa USa OSa OPSa ba)
    (Tb : BitVec 64) (Eb : BitVec 64 → Prop) (KLb SDb Cb Nb KSb VSb USb OSb OPSb : BitVec 64) (bb : Nat)
    (layB : HLay P0 Tb Eb KLb SDb Cb Nb KSb VSb USb OSb OPSb bb)
    (sepB : ∀ x : BitVec 64, (x = Bs + 72 ∨ (Tb.toNat ≤ x.toNat ∧ x.toNat < Tb.toNat + 72)) → ¬ Foot P0 Ta Ea x)
    (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (oK : ¬ MWin K 200 w) (oP : ¬ MWin Pd 136 w)
    (oN : ∀ j : Nat, j < 64 → w ≠ panByteAlignHOL (NB + BitVec.ofNat 64 j))
    (hsc : w.toNat < FM.toNat ∨ SP0.toNat ≤ w.toNat) (hp : w.toNat < P0.toNat)
    (hwA : ¬ Foot P0 Ta Ea w) (hwB : ¬ Foot P0 Tb Eb w)
    {F : Type} (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode) (dom : DomOK s.memaddrs)
    (aw : AW SP0 P0 FM G0 s.globals) (sl : SL (fun x => x ≠ ofString "w") s.locals)
    (pre : PreStateP Ts Bs Ta KLa SDa Ca Na KSa VSa USa OSa OPSa Tb KLb SDb Cb Nb KSb VSb USb OSb OPSb s.locals s.memory) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_get_pre_state_account_optional)).2.memory w =
        s.memory w ∧
      (Continuing (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_get_pre_state_account_optional)).1 →
        AW SP0 P0 FM G0 (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_get_pre_state_account_optional)).2.globals) :=
  let h := preState_aqm Ts Bs hTs hBs Ta Ea KLa SDa Ca Na KSa VSa USa OSa OPSa ba layA Tb Eb KLb SDb Cb Nb KSb VSb USb
    OSb OPSb bb layB sepB K Pd NB hK0 hPd0 hNB0 oK oP oN hsc hp hwA hwB F s code dom aw sl pre
  ⟨h.1,h.2.1⟩

#print axioms aqm_setCall
#print axioms recordPreRead_aqm
#print axioms preState_aqm
#print axioms preState_frame
end InitECandidate.Runtime
