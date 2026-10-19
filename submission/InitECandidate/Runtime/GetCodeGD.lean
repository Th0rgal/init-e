import InitECandidate.Runtime.OriginalTxCheckCode
import InitECandidate.Runtime.GlobalKeepAllProgram
import InitECandidate.Runtime.DestroyStorageGD
/-!
Original `get_code(code_hash, addr)` over the content-carrying registry `RegT` in the fixed-domain triple: the
read-only `memeq`, `htab_get` (code caches `ts + 48`, `bs + 48`) and `ws_get_code` through the whole-program memory and
globals frames (`memoryFrame_of_good`), `sk_make` into the key buffer, and `htab_set` on the code-read table (cell
`ts + 40`) re-establishing `RegT` (`regT_set`). `aqgd_callAssignF`: a call assigning any-shape result to a local outside
`Vn`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A call assigning its (any-shape) result to a local outside `Vn`, against a callee spec. -/
theorem aqgd_callAssignF {Vn' : MlS → Prop} {P Q : GA → Mem → GA → Prop}
    (Pe : GA → Mem → GA → GA → Mem → GA → Prop) (RRe : GA → Mem → GA → ValueHOL 64 → Mem → GA → Prop)
    (name function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (hvn : ¬ Vn name)
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQGD D B A w Vn' (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hret : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → Q (L.update (name,v)) M' H') :
    AQGD D B A w Vn P Q RR (.call (some (some (.local,name),none)) function arguments) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
    | some data =>
      obtain ⟨found,callee,foundShape⟩ := data
      dsimp only
      have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body found returnShape
        foundShape values callee (by rw [code]; exact installed) lookup
      subst same
      have lookup' : lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (found,callee,foundShape) := by
        rw [← code]; exact lookup
      have esl := callee_entry_sl function values parameters found returnShape installed allOne found callee foundShape
        lookup'
      split
      · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (sl_mono esl (fun _ _ => trivial)) H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          rcases rb with _ | (_ | _ | _ | _ | v | _ | _)
          all_goals (dsimp only)
          all_goals (try split)
          all_goals (try split)
          all_goals first
            | (obtain ⟨H',hH',rr⟩ := r1 _ rfl
               exact ⟨m1,fun _ => a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩))),
                fun _ => ⟨sl_update sl _ _ (fun hn => absurd hn hvn),H',hH',hret _ _ _ _ _ _ pre rr⟩,
                (fun v e => by cases e),by simp,by simp⟩)
            | exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

#print axioms aqgd_callAssignF
variable {SP0 P0 FM : BitVec 64} {G0 : GA}

/-- Exit of `get_code`: heap not below the entry heap, the registry with content at the exit heap, counter unchanged,
outside words outside the key buffer kept. -/
def GCPost (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (SKB H0 Nj : BitVec 64) (M0 : Mem) (M' : Mem) (G' : GA) : Prop :=
  ∃ H' : BitVec 64, HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ RegT n c T Out H' M' D B ko ∧
    G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ SkWin SKB x → M' x = M0 x

section gc
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko k40 : Fin n}
  {Ts SKB J C Nj H0 : BitVec 64} {M0 : Mem}

set_option maxHeartbeats 16000000 in
/-- The original `get_code(code_hash, addr)` over the content-carrying registry: the read-only lookups (`memeq`,
`htab_get` on `ts + 48` and `bs + 48`), `sk_make` into the key buffer, `htab_set` on the code-read table `k40`
(cell `ts + 40`), and the memory-keeping `ws_get_code`: every return satisfies `GCPost`. -/
theorem getCodeT_aqgd (ne : k40 ≠ ko) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hc40 : c k40 = Ts + 40#64) (p0 : P0.toNat ≤ H0.toNat) (hwP : w.toNat < P0.toNat) (hOut : Out w)
    (hwS : ¬ SkWin SKB w) (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun x => x ≠ ofString "w" ∧ x ≠ ofString "c")
      (fun L M G => ((∃ Ch : BitVec 64, L.lookup (ofString "code_hash") = some (.val (.word Ch))) ∧
        (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A)))) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => GCPost n c T Out ko D B SKB H0 Nj M0 M' G')
      (sourceFunctionBody Guest.guestFn_get_code) := by
  -- the pointer cell `ts + 40` through the static global `ts`
  have cellEv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (k : Fin n) (off : BitVec 64), c k = Ts + off →
      JWS SP0 P0 FM G0 J C SKB s.globals → s.memory (c k) = .word (T k) → ∀ v,
      EV s (.load .one (.op .add [.var .global (ofString "ts"),.const off])) = some v → v = .val (.word (T k)) := by
    intro F s k off hc aw hm v ev
    obtain ⟨eg,_⟩ := aw.1.1.2.2.2 (ofString "ts") (by decide)
    rw [hc] at hm
    simp [EV,evalHOLExact,evalListHOLExact,eg,hTs,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,hm] at ev
    exact ev.2.symm
  let GL : GA → Prop := fun L => (∃ Ch : BitVec 64, L.lookup (ofString "code_hash") = some (.val (.word Ch))) ∧
    (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A)))
  have gl_upd : ∀ L x v, x ≠ ofString "code_hash" → x ≠ ofString "addr" → GL L → GL (L.update (x,v)) := by
    intro L x v h1 h2 ⟨⟨Ch,hC⟩,⟨A,hA⟩⟩
    exact ⟨⟨Ch,by simp [HolFiniteMapExact.lookup_update,FUPDATE,h1,hC]⟩,
      ⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE,h2,hA]⟩⟩
  have gl_res : ∀ L x o, x ≠ ofString "code_hash" → x ≠ ofString "addr" → GL L → GL (L.resVarEq (x,o)) := by
    intro L x o h1 h2 ⟨⟨Ch,hC⟩,⟨A,hA⟩⟩
    exact ⟨⟨Ch,by rw [resVar_lookup_ne _ _ _ _ (Ne.symm h1)]; exact hC⟩,⟨A,by rw [resVar_lookup_ne _ _ _ _ (Ne.symm h2)]; exact hA⟩⟩
  -- the state kept until the key-buffer write: unchanged memory and globals
  let S0 : GA → Mem → GA → Prop := fun L M G => GL L ∧
    RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj))
  have post0 : ∀ M G, S0 (HolFiniteMapExact.empty) M G → GCPost n c T Out ko D B SKB H0 Nj M0 M G := by
    intro M G ⟨_,reg,hM,hH,hn⟩
    exact ⟨H0,hH,le_refl _,reg,hn,fun x _ _ => by rw [hM]⟩
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_get_code,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some]
  have dsm0 : ∀ M G, S0 (HolFiniteMapExact.empty) M G → DSM n c T Out ko D B SKB H0 Nj M0 M G := by
    intro M G ⟨_,reg,hM,hH,hn⟩
    exact ⟨H0,hH,le_refl _,reg,hn,fun x _ _ => by rw [hM]⟩
  have retOK : ∀ L M G, S0 L M G → GCPost n c T Out ko D B SKB H0 Nj M0 M G := by
    intro L M G ⟨_,reg,hM,hH,hn⟩
    exact ⟨H0,hH,le_refl _,reg,hn,fun x _ _ => by rw [hM]⟩
  -- eq = memeq(code_hash, empty_code_hash, 32): read-only
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := S0) (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_memeq_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf (memoryFrame_of_good originalRuntimeCode_memeq_lookup (by decide) (by decide))
      (by body_check Guest.guestFn_memeq) (by body_check Guest.guestFn_memeq) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨gl,rest⟩ ⟨e1,e2⟩ _
    subst e1 e2
    exact ⟨gl_upd L _ v (by decide) (by decide) gl,rest⟩
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_return _ (fun s v H _ hG ⟨pre,_⟩ _ _ => retOK _ _ _ pre))
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h))) ?_
  -- w = htab_get(lds (ts + 48), code_hash): read-only
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := S0) (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => absurd rfl h.1) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨gl,rest⟩ ⟨e1,e2⟩ _
    subst e1 e2
    exact ⟨gl_upd L _ v (by decide) (by decide) gl,rest⟩
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_return _ (fun s v H _ hG ⟨pre,_⟩ _ _ => retOK _ _ _ pre))
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h))) ?_
  -- w = htab_get(lds (bs + 48), code_hash): read-only
  refine aqgd_seq (Q := S0) (aqgd_callAssignF (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp) (fun h => absurd rfl h.1)
    (fun _ M0' G0' _ => aqgd_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) ?_) ?_
  · intro L M G v M' G' ⟨gl,rest⟩ ⟨e1,e2⟩
    subst e1 e2
    exact ⟨gl_upd L _ v (by decide) (by decide) gl,rest⟩
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_return _ (fun s v H _ hG ⟨pre,_⟩ _ _ => retOK _ _ _ pre))
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h))) ?_
  -- k = sk_make(addr, code_hash); htab_set(lds (ts + 40), k, 1); c = ws_get_code(code_hash); return c
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' L M G => (∃ a k : BitVec 64, L.lookup (ofString "addr") = some (.val (.word a)) ∧
      L.lookup (ofString "key") = some (.val (.word k))) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ M0' G0' v M' G' => v = .val (.word SKB) ∧ G' = G0' ∧ ∀ x, ¬ SkWin SKB x → M' x = M0' x)
    (Pc := fun L M G => (GL L ∧ L.lookup (ofString "k") = some (.val (.word SKB))) ∧
      DSM n c T Out ko D B SKB H0 Nj M0 M G)
    (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ vmLookup_sk_make (by simp) (fun _ M0' G0' _ => skMake_aqgd (fun g h => h.2) hwS M0' G0')
    ?_ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ G hG ⟨⟨⟨Ch,hC⟩,⟨A,hA⟩⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA,hC] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) vmLookup_sk_make] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,Ch,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨gl,reg,hM,hH,hn⟩ ⟨ev,eG,fr⟩ _
    subst ev eG hM
    refine ⟨⟨gl_upd L _ _ (by decide) (by decide) gl,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
      H0,hH,le_refl _,regT_frame reg (SkWin SKB) hSO (fun x hx => fr x hx),hn,fun x _ hsk => fr x hsk⟩
  refine aqgd_seq (Q := fun L M G => GL L ∧ DSM n c T Out ko D B SKB H0 Nj M0 M G) ?_ ?_
  · refine aqgd_conseq (P := fun L M G => ∃ q : (Fin n → TLay) × BitVec 64,
        (GL L ∧ L.lookup (ofString "k") = some (.val (.word SKB))) ∧ HeapIs G q.2 ∧ H0.toNat ≤ q.2.toNat ∧
        RegPure n c T Out q.2 q.1 ∧ RegMem n c T q.1 M ∧ TCont D B M (T ko) (q.1 ko) ∧
        (∀ x, (q.1 ko).arr x → x.toNat < q.2.toNat) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∀ x, Out x → ¬ SkWin SKB x → M x = M0 x)
      (aqgd_ex (fun q => ?_)) (fun L M G ⟨hl,H,hH,hle,⟨l,pure,mem,tc,ab⟩,hn,fr⟩ =>
        ⟨(l,H),hl,hH,hle,pure,mem,tc,ab,hn,fr⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
    rcases q with ⟨l,H⟩
    dsimp only
    refine aqgd_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' G0' L M G => LK (irP0 (T k40) SKB 1#64) L ∧ M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' _ M' G' => G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∃ H' : BitVec 64, HeapIs G' H' ∧ SetPost (T k40) ((l k40).canon (T k40) H) M0' (l k40).C (l k40).SD
          (l k40).KS (l k40).VS (l k40).US (l k40).OS (l k40).OPS H M' H')
      _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ ?_
    · intro L0 M0' G0' ⟨_,hH,hle,pure,mem,_,_,hn,_⟩
      have lay := (pure.1 k40).1
      have hwk : ¬ (l k40).canon (T k40) H w := pure.2.2 w hOut k40
      have p2 : P0.toNat ≤ H.toNat := by omega
      refine aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
        originalRuntimeCode_hashSet_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
        (aqmh_rebound (set_aqmh (P0 := H) (T k40) SKB 1#64 _ (l k40).KL (l k40).SD (l k40).C (l k40).N (l k40).KS
          (l k40).VS (l k40).US (l k40).OS (l k40).OPS (l k40).b lay M0' hwk H (le_refl _)) p2)))
        (keepsSkBuf_of_installed originalRuntimeCode_hashSet_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
      · intro L M G ⟨hl,hM,hG⟩
        subst hM hG
        exact ⟨hn,H,hH,le_refl _,hl,(mem k40).2,rfl,rfl⟩
      · intro v M' G' ⟨hn',H',hH',post⟩
        exact ⟨hn',H',hH',post⟩
    · intro F s values callee rs aw G hG ⟨⟨_,hk⟩,_,_,_,mem,_⟩ _ args lookup
      unfold GIs at hG; subst hG
      rw [evalListHOLFinite_eq_toExact] at args
      cases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
          (.load .one (.op .add [.var .global (ofString "ts"),.const 40#64])) with
      | none => simp [evalListHOLExact,h1] at args
      | some x1 =>
        have e1 := cellEv s k40 40#64 hc40 aw (mem k40).1 x1 h1
        subst e1
        simp only [evalListHOLExact,h1] at args
        simp [evalListHOLExact,evalHOLExact,hk] at args
        subst args
        rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
          originalRuntimeCode_hashSet_lookup] at lookup
        simp only [Option.some.injEq,Prod.mk.injEq] at lookup
        obtain ⟨_,rfl,_⟩ := lookup
        refine ⟨fun p hp => ?_,rfl,rfl⟩
        simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
        rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
    · intro L M G v M' G' ⟨hl,hH,hle,pure,mem,tc,ab,hn,frO⟩ ⟨hn',H',hH',post⟩
      exact ⟨hl.1,H',hH',le_trans hle post.1,regT_set ne l pure mem tc ab post,hn',
        fun x ho hsk => (post.2.1 x (pure.2.2 x ho k40)).trans (frO x ho hsk)⟩
  -- c = ws_get_code(code_hash): memory-keeping; return c
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => GL L ∧ DSM n c T Out ko D B SKB H0 Nj M0 M G) (Qc := fun _ _ _ => False)
    _ _ _ _ _ _ _ originalRuntimeCode_wsGetCode_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf (memoryFrame_of_good originalRuntimeCode_wsGetCode_lookup (by decide) (by decide))
      (by body_check Guest.guestFn_ws_get_code) (by body_check Guest.guestFn_ws_get_code) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => absurd rfl h.2) ?_
    (aqgd_return _ (fun s v H _ hG ⟨_,H',hH',hle,reg,hn,fr⟩ _ _ => ⟨H',hH',hle,reg,hn,fr⟩))
    (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨gl,rest⟩ ⟨e1,e2⟩ _
    subst e1 e2
    exact ⟨gl_upd L _ v (by decide) (by decide) gl,rest⟩
#print axioms getCodeT_aqgd
end gc
end InitECandidate.Runtime
