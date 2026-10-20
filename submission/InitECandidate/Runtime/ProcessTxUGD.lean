import InitECandidate.Runtime.CheckTransactionUGD
import InitECandidate.Runtime.ProcessTxWritersGD
/-!
The `process_transaction` prefix and sender-debit segment over the arena that also pins the `u256_ws` workspace pointer
(`JWSBU`), with `FrameCU` callee contracts; `processTx_to_teNew_final` discharges the `check_transaction` and
`calculate_blob_gas_price` contracts, leaving `encode_transaction` and `recover_sender_with_chain_id`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- `JWSB` with the `u256_ws` workspace pointer pinned to `U`. -/
def JWSBU (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB Bo U : BitVec 64) (g : GA) : Prop :=
  JWSB SP0 P0 FM G0 J C SKB Bo g ∧ WsG U g

section liftu
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U : BitVec 64} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64}

theorem aqgd_jwsbu (h : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w Vn P Q RR p)
    (hkb : keepsG (ofString "bo") goodBo p = true) (hkw : keepsG (ofString "u256_ws") goodWs p = true) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w Vn P Q RR p :=
  aqgd_conseq (aqgd_strengthen (X := WsG U) (aqgd_jwsb (Bo := Bo) h hkb)
    (fun s code x => (evaluate_keeps_ws p hkw s code).trans x)) (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h)

theorem aqgd_jwsbu_of_u (h : AQGD D B (JWSU SP0 P0 FM G0 J C SKB U) w Vn P Q RR p)
    (hkb : keepsG (ofString "bo") goodBo p = true) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w Vn P Q RR p := by
  have h2 := aqgd_strengthen (X := fun g => g.lookup (ofString "bo") = some (.val (.word Bo))) h
    (fun s code x => (evaluate_keeps_bo p hkb s code).trans x)
  intro F s code dom aw sl H hH pre
  obtain ⟨m,a,n,r,c,b⟩ := h2 F s code dom ⟨⟨aw.1.1,aw.2⟩,aw.1.2⟩ sl H hH pre
  exact ⟨m,fun e => ⟨⟨(a e).1.1,(a e).2⟩,(a e).1.2⟩,n,r,c,b⟩

#print axioms aqgd_jwsbu
#print axioms aqgd_jwsbu_of_u
end liftu

section wru
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {Excl : BitVec 64 → Prop}
  {J C SKB Bo H0 U : BitVec 64} {M0 : Mem}

/-- A global assignment to a name outside the arena, journal, key-buffer, `bo`, `u256_ws` and heap/counter names
keeps `PXR` on the pinned arena. -/
theorem aqgd_assignGlobal_otherU {LP : GA → Prop} (name : MlS) (e : ExpHOL 64)
    (hn : name ∉ [ofString "frame_mem_ptr",ofString "scratch_ptr",ofString "heap_ptr",ofString "journal",
      ofString "journal_cap",ofString "sk_buf",ofString "bo",ofString "journal_n"]) (hs : name ∉ staticGlobalNames)
    (hk : keepsG (ofString "u256_ws") goodWs (.assign .global name e) = true) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) RR (.assign .global name e) :=
  aqgd_strengthen (X := WsG U) (aqgd_assignGlobal_other (w := w) (Bo := Bo) name e hn hs)
    (fun s code x => (evaluate_keeps_ws _ hk s code).trans x)

#print axioms aqgd_assignGlobal_otherU
end wru

section fcu
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {Excl : BitVec 64 → Prop}
  {J C SKB Bo H0 U : BitVec 64} {M0 : Mem}

/-- A declared call to a callee with a frame contract, preserving `PXR` and a locals predicate stable under the new
local. -/
theorem aqgd_decCall_fcU {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (fc : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl body) (hk : keepsG (ofString "bo") goodBo body = true)
    (hup : ∀ L v, LP L → shapeEqHOL (shapeOfHOLExact v) shape = true → LP' (L.update (name,v)))
    (hcont : AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LP' L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q RR cont)
    (hres : ∀ L M G L' M' G', LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q2 RR (.decCall name shape function arguments cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1 Nj : BitVec 64, HeapIs G0' H1 ∧ G0'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧ RegT n c T Out H' M' D B ko ∧
          G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ Excl x → M' x = M0' x)
    (Pc := fun L M G => LP' L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (Qc := Q)
    _ _ _ _ _ _ _ installed allOne ?_ (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ hcont hres
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,_,reg,hn,_⟩
    refine aqgd_conseq (aqgd_jwsbu_of_u (fc H1 Nj M0') hk) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hM,hG⟩
      subst hM hG
      exact ⟨reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,Nj,hH,hn,post⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,hle,_,_,fr⟩ ⟨H1',Nj',hH',_,H',hH2,hle',reg',hn',fr'⟩ ok
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨hup L v lp ok,H',Nj',hH2,le_trans hle hle',reg',hn',fun x ho hx => (fr' x ho hx).trans (fr x ho hx)⟩

/-- A discarded call to a callee with a frame contract. -/
theorem aqgd_call_fcU {LP : GA → Prop} (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (fc : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl body) (hk : keepsG (ofString "bo") goodBo body = true) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) RR (.call (some (none,none)) function arguments) := by
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1 Nj : BitVec 64, HeapIs G0' H1 ∧ G0'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧ RegT n c T Out H' M' D B ko ∧
          G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ Excl x → M' x = M0' x)
    _ _ _ _ _ installed allOne ?_ (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) ?_
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,_,reg,hn,_⟩
    refine aqgd_conseq (aqgd_jwsbu_of_u (fc H1 Nj M0') hk) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hM,hG⟩
      subst hM hG
      exact ⟨reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,Nj,hH,hn,post⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,hle,_,_,fr⟩ ⟨H1',Nj',hH',_,H',hH2,hle',reg',hn',fr'⟩
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨lp,H',Nj',hH2,le_trans hle hle',reg',hn',fun x ho hx => (fr' x ho hx).trans (fr x ho hx)⟩

#print axioms aqgd_decCall_fcU
#print axioms aqgd_call_fcU
end fcu

section wru
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {Excl : BitVec 64 → Prop}
  {J C SKB Bo H0 U : BitVec 64} {M0 : Mem}

/-- A word-valued declared allocation: the heap grows, memory is unchanged, `PXR` is kept. -/
theorem aqgd_decCall_allocU {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name : MlS) (sz : BitVec 64)
    {cont : ProgHOL 64}
    (hup : ∀ L (y : BitVec 64), LP L → LP' (L.update (name,.val (.word y))))
    (hcont : AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LP' L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q RR cont)
    (hres : ∀ L M G L' M' G', LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q2 RR
      (.decCall name .one (ofString "alloc") [.const sz] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      L.lookup (ofString "n") = some (.val (.word sz)) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (v : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1 Nj : BitVec 64, HeapIs G0' H1 ∧ G0'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        ∃ H', HeapIs G' H' ∧ M' = M0' ∧ v = .val (.word H1) ∧ H1.toNat ≤ H'.toNat)
    (Pc := fun L M G => LP' L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (Qc := Q)
    _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hcont hres
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,_,_,hn,_⟩
    refine aqgd_conseq (aqgd_jwsbu (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_allocation_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) sz H1 M0')))
      (keepsSkBuf_of_installed originalRuntimeCode_allocation_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_allocation_lookup (by decide)) (keepsWs_of_installed originalRuntimeCode_allocation_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hl,hM,hG⟩
      subst hM hG
      exact ⟨hn,H1,hH,hl,rfl,rfl⟩
    · intro v M' G' ⟨hn',H',hH',eM,ev,_,_,c1,_⟩
      exact ⟨H1,Nj,hH,hn,hn',H',hH',eM,ev,by omega⟩
  · intro F s values callee rs _ H _ _ _ args lookup
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,hle,reg,hn,fr⟩ ⟨H1',Nj',hH',hn1,hn',H',hH2,eM,ev,hle'⟩ _
    have e := heapIs_unique hH hH'
    subst e ev eM
    refine ⟨hup L _ lp,H',Nj',hH2,le_trans hle hle',regT_mono reg hle',hn',fr⟩

#print axioms aqgd_decCall_allocU

end wru

section wr2u
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {Excl : BitVec 64 → Prop}
  {J C SKB Bo H0 U : BitVec 64} {M0 : Mem}

/-- A word store into an exception-region outside word (not a pointer cell) keeps `PXR`. -/
theorem aqgd_store_exclU {LP : GA → Prop} (d v : ExpHOL 64) (a : BitVec 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), JWSBU SP0 P0 FM G0 J C SKB Bo U s.globals → DomD D B s →
      LP s.locals → PXR n c T Out ko D B Excl H0 M0 s.memory s.globals → EV s d = some (.val (.word a)))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals → EV s v = some x →
      ∃ y : BitVec 64, x = .val (.word y))
    (hwa : w ≠ a) (hOutA : Out a ∧ ∀ i, a ≠ c i) (hExA : Excl a) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) RR (.store d v) := by
  refine aqgd_storeD _ _ (fun s H aw dom hG ⟨lp,px⟩ _ => ?_) (fun s x H _ _ _ ⟨lp,_⟩ _ ev => hv s x lp ev)
  unfold GIs at hG; subst hG
  obtain ⟨H1,Nj,hH,hle,reg,hn,fr⟩ := px
  refine ⟨a,hd s aw dom lp ⟨H1,Nj,hH,hle,reg,hn,fr⟩,hwa,fun y _ => ⟨lp,H1,Nj,hH,hle,?_,hn,fun x ho hx => ?_⟩⟩
  · exact regT_frame reg (fun x => x = a) (fun x hx => by subst hx; exact hOutA) (fun x hx => by simp [hx])
  · have : x ≠ a := fun e => hx (e ▸ hExA)
    simp only [if_neg this]
    exact fr x ho hx

#print axioms aqgd_store_exclU
end wr2u

section gau
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo H0 Ts Bs U : BitVec 64} {M0 : Mem}

/-- A declared `get_account(x)` call (account read tables `kA`, `kB`) keeping `PXR`: the registry with the content
of `ko` and every outside word (all outside words are off the workspace and below `P0`). -/
theorem aqgd_decCall_getAccountU {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name xname : MlS)
    {cont : ProgHOL 64}
    (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hOut : Out w) (hwP : w.toNat < P0.toNat)
    (p0 : P0.toNat ≤ H0.toNat) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hx : ∀ L, LP L → ∃ X : BitVec 64, L.lookup xname = some (.val (.word X)))
    (hup : ∀ L (y : BitVec 64), LP L → LP' (L.update (name,.val (.word y))))
    (hcont : AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LP' L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q RR cont)
    (hres : ∀ L M G L' M' G', LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q2 RR
      (.decCall name .one (ofString "get_account") [.var .local xname] cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ (H1 Nj : BitVec 64) (l : Fin n → TLay), HeapIs G0' H1 ∧ G0'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
        RegPure n c T Out H1 l ∧ RegMem n c T l M0' ∧ TCont D B M0' (T ko) (l ko) ∧
        (∀ x, (l ko).arr x → x.toNat < H1.toNat) ∧
        (G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H', HeapIs G' H' ∧
          ((Reg n c T Out H' M' ∧ H1.toNat ≤ H'.toNat) ∧
            ∀ x, GaKeep SP0 P0 FM K Pd NB Out (T ko) (l ko) x → M' x = M0' x)))
    (Pc := fun L M G => LP' L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (Qc := Q)
    _ _ _ _ _ _ _ originalRuntimeCode_account_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hcont hres
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,h01,⟨l,pure,mem,tc,ab⟩,hn,_⟩
    have p1 : P0.toNat ≤ H1.toNat := le_trans p0 h01
    refine aqgd_conseq (aqgd_jwsbu (aqgd_jws (aqgd_of_aqg (aqg_withA (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_account_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (accountRegT_aqmh n c T kA kB ko hAB hAo hBo Ts Bs hTs hBs hcA hcB Out hOut H1 p1 K Pd NB hK0 hPd0 hNB0
        safe (hOutSafe w hOut).1 hwP l pure M0' mem ab))))
      (keepsSkBuf_of_installed originalRuntimeCode_account_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_account_lookup (by decide)) (keepsWs_of_installed originalRuntimeCode_account_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨hn,H1,hH,⟨ha,rfl,l,reg_of pure mem,pure.2.1,pure.2.2⟩,rfl⟩
    · intro v M' G' ⟨post,_⟩
      exact ⟨H1,Nj,l,hH,hn,pure,mem,tc,ab,post⟩
  · intro F s values callee rs _ H _ ⟨lp,_⟩ _ args lookup
    obtain ⟨X,hX⟩ := hx _ lp
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hX] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_account_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨X,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,hle,_,_,fr⟩ ⟨H1',Nj',l,hH',_,pure,mem,tc,ab,hn',H',hH2,⟨reg,hle'⟩,frG⟩ ok
    have e := heapIs_unique hH hH'
    subst e
    obtain ⟨y,rfl⟩ := scalar_of_shape' ok
    have keepT : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
        M' x = M x := fun x hx => frG x (Or.inl ⟨hx,hkoWs M (l ko) (mem ko).2 x hx⟩)
    exact ⟨hup L y lp,H',Nj',hH2,le_trans hle hle',regT_of_reg l pure tc ab reg hle' keepT,hn',
      fun x ho hxe => (frG x (Or.inr ⟨ho,hOutSafe x ho⟩)).trans (fr x ho hxe)⟩

#print axioms aqgd_decCall_getAccountU
end gau

section pxu
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo H0 Ts Bs U : BitVec 64} {M0 : Mem}

/-- The actual `process_transaction` body from `bal_index = index + 1` (just after `state_fresh_tx()`) to the
`increment_nonce(sender)` call: from the content-carrying registry `PXR` and the `index` word, every path either
leaves early (raise/error, frames kept by each step) or reaches the `increment_nonce` site with `PXR`, `index` and a
one-word `sender`. Real specs: `bal_index` assignment, the two block-output transaction-array stores (into `Excl`),
`alloc`, `get_account` (registry with `ko` content), and the read-only callees `tx_chain_id`,
`validate_transaction`, `calculate_total_blob_gas`, `fee_mul`, `min` (whole-program memory/globals decisions).
Temporary scoped frame contracts (remaining obligations): `encode_transaction`, `recover_sender_with_chain_id`,
`check_transaction`, `calculate_blob_gas_price`. -/
theorem processTx_prefix_aqgdU {QM : Mem → GA → Prop} (Ix Arr : BitVec 64)
    -- temporary scoped callee frame contracts (named obligations)
    (fcEnc : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_encode_transaction))
    (fcRec : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_recover_sender_with_chain_id))
    (fcChk : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_check_transaction))
    (fcBgp : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_calculate_blob_gas_price))
    -- the block-output transaction array cell and the two written words
    (hBoD : D (Bo + 24)) (hBoO : Out (Bo + 24)) (hBoE : ¬ Excl (Bo + 24)) (hArr : M0 (Bo + 24) = .word Arr)
    (hO0 : Out (Arr + Ix * 16) ∧ ∀ i, Arr + Ix * 16 ≠ c i) (hE0 : Excl (Arr + Ix * 16)) (hw0 : w ≠ Arr + Ix * 16)
    (hO8 : Out (Arr + Ix * 16 + 8) ∧ ∀ i, Arr + Ix * 16 + 8 ≠ c i) (hE8 : Excl (Arr + Ix * 16 + 8))
    (hw8 : w ≠ Arr + Ix * 16 + 8)
    -- get_account registry premises
    (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hOut : Out w) (hwP : w.toNat < P0.toNat)
    (p0 : P0.toNat ≤ H0.toNat) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hrest : AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 28 (sourceFunctionBody Guest.guestFn_process_transaction))) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_process_transaction)) := by
  unfold sourceFunctionBody at hrest ⊢
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq] at hrest ⊢
  simp only [Guest.guestFn_process_transaction,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,stateInitSpineDrop] at hrest ⊢
  -- bal_index = index + 1
  refine aqgd_seq (aqgd_assignGlobal_otherU _ _ (by decide) (by decide) (by decide)) ?_
  -- enc = encode_transaction(tx)
  refine aqgd_decCall_fcU (LP' := LPE Ix) _ _ _ _ _ _ _ originalRuntimeCode_encodeTransaction_lookup (by simp) fcEnc
    (keepsBo_of_installed originalRuntimeCode_encodeTransaction_lookup (by decide))
    (fun L v lp ok => ⟨lpi_upd lp _ v (by decide),by
      obtain ⟨a,b,rfl⟩ := pair_of_shape ok
      exact ⟨a,b,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩⟩) ?_ (fun _ _ _ _ _ _ _ h => h)
  -- the two block-output transaction-array stores
  have arr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), JWSBU SP0 P0 FM G0 J C SKB Bo U s.globals → DomD D B s →
      PXR n c T Out ko D B Excl H0 M0 s.memory s.globals →
      s.globals.lookup (ofString "bo") = some (.val (.word Bo)) ∧ s.memaddrs (Bo + 24) ∧ s.memory (Bo + 24) = .word Arr :=
    fun s aw dom ⟨_,_,_,_,_,_,fr⟩ => ⟨aw.1.2,dom.2.1 ▸ hBoD,(fr _ hBoO hBoE).trans hArr⟩
  refine aqgd_seq (aqgd_store_exclU _ _ _ (fun s aw dom lp px => ?_) (fun s x lp ev => ?_) hw0 hO0 hE0) ?_
  · obtain ⟨hb,hd,hm⟩ := arr s aw dom px
    have hd' : s.memaddrs (Bo + 24#64) := hd
    have hm' : s.memory (Bo + 24#64) = .word Arr := hm
    have hi := lp.1
    unfold LPI at hi
    simp [EV,evalHOLExact,evalListHOLExact,hb,hd',hm',hi,memLoadHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,
      panOpHOL]
  · obtain ⟨_,a,b,he⟩ := lp
    simp [EV,evalHOLExact,he] at ev
    exact ⟨a,ev.symm⟩
  refine aqgd_seq (aqgd_store_exclU _ _ _ (fun s aw dom lp px => ?_) (fun s x lp ev => ?_) hw8 hO8 hE8) ?_
  · obtain ⟨hb,hd,hm⟩ := arr s aw dom px
    have hd' : s.memaddrs (Bo + 24#64) := hd
    have hm' : s.memory (Bo + 24#64) = .word Arr := hm
    have hi := lp.1
    unfold LPI at hi
    simp [EV,evalHOLExact,evalListHOLExact,hb,hd',hm',hi,memLoadHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,
      panOpHOL,BitVec.add_assoc]
  · obtain ⟨_,a,b,he⟩ := lp
    simp [EV,evalHOLExact,he] at ev
    exact ⟨b,ev.symm⟩
  refine aqgd_seq aqgd_skip ?_
  -- cid = tx_chain_id(tx)
  refine aqgd_decCall_mf (I' := fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) _ _ _ _ _ _ _
    originalRuntimeCode_txChainId_lookup (by simp)
    (memoryFrame_of_good originalRuntimeCode_txChainId_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_tx_chain_id) (by body_check Guest.guestFn_tx_chain_id)
    (fun L M G v ⟨lp,px⟩ => ⟨lpi_upd lp.1 _ v (by decide),px⟩) ?_ (fun _ _ _ _ _ _ _ h => h)
  -- chain-id check: raises or falls through
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
    (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_raise _ _)
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1.1) (fun _ _ _ h => h) (fun _ _ _ h => h)))
    (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  -- sender = alloc(24)
  refine aqgd_decCall_allocU (LP' := LPS Ix) _ _
    (fun L y lp => ⟨lpi_upd lp _ _ (by decide),y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  -- recover_sender_with_chain_id(tx, chain id, sender)
  refine aqgd_seq (aqgd_call_fcU _ _ _ _ _ originalRuntimeCode_recoverSender_lookup (by simp) fcRec
    (keepsBo_of_installed originalRuntimeCode_recoverSender_lookup (by decide))) ?_
  refine aqgd_seq aqgd_skip ?_
  -- intrinsic = validate_transaction(tx, sender)
  refine aqgd_decCall_mf (I' := fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) _ _ _ _ _ _ _
    originalRuntimeCode_validateTransaction_lookup (by simp)
    (memoryFrame_of_good originalRuntimeCode_validateTransaction_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_validate_transaction) (by body_check Guest.guestFn_validate_transaction)
    (fun L M G v ⟨lp,px⟩ => ⟨lps_upd lp _ v (by decide) (by decide),px⟩) ?_ (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq aqgd_skip ?_
  -- intrinsic_gas
  refine aqgd_dec_lps _ _ _ (by decide) (by decide) ?_
  -- price = check_transaction(tx, sender)
  refine aqgd_decCall_fcU (LP' := LPS Ix) _ _ _ _ _ _ _ originalRuntimeCode_checkTransaction_lookup (by simp) fcChk
    (keepsBo_of_installed originalRuntimeCode_checkTransaction_lookup (by decide))
    (fun L v lp _ => lps_upd lp _ v (by decide) (by decide)) ?_ (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq aqgd_skip ?_
  -- tx_blob_gas_used = calculate_total_blob_gas(tx)
  refine aqgd_decCall_lps _ _ _ _ _ _ _ originalRuntimeCode_totalBlobGas_lookup
    (memoryFrame_of_good originalRuntimeCode_totalBlobGas_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_calculate_total_blob_gas) (by body_check Guest.guestFn_calculate_total_blob_gas)
    (by decide) (by decide) ?_
  -- acct = get_account(sender)
  refine aqgd_decCall_getAccountU (LP' := LPS Ix) _ _ hAB hAo hBo hTs hBs hcA hcB hOut hwP p0 K Pd NB hK0 hPd0 hNB0
    safe hOutSafe hkoWs (fun _ lp => lp.2) (fun L y lp => lps_upd lp _ _ (by decide) (by decide)) ?_
    (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq aqgd_skip ?_
  refine aqgd_dec_lps _ _ _ (by decide) (by decide) ?_
  -- blob gas fee branch
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
    (aqgd_conseq (aqgd_decCall_fcU (LP' := LPS Ix) (Q := fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      _ _ _ _ _ _ _ originalRuntimeCode_blobGasPrice_lookup (by simp) fcBgp
      (keepsBo_of_installed originalRuntimeCode_blobGasPrice_lookup (by decide))
      (fun L v lp _ => lps_upd lp _ v (by decide) (by decide))
      (aqgd_decCall_lpsR _ _ _ _ _ _ _ originalRuntimeCode_feeMul_lookup
        (memoryFrame_of_good originalRuntimeCode_feeMul_lookup (by decide) (by decide))
        (by body_check Guest.guestFn_fee_mul) (by body_check Guest.guestFn_fee_mul) (by decide) (by decide)
        (aqgd_assignLocal _ _ (fun _ v _ _ pre _ _ => ⟨lps_upd pre.1 _ v (by decide) (by decide),pre.2⟩)))
      (fun _ _ _ _ _ _ _ h => ⟨lps_res h.1 _ _ (by decide) (by decide),h.2⟩))
      (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  -- gas, egf = fee_mul(gas, price), effective_gas_fee, execution_gas, regular_budget
  refine aqgd_dec_lps _ _ _ (by decide) (by decide) ?_
  refine aqgd_decCall_lps _ _ _ _ _ _ _ originalRuntimeCode_feeMul_lookup
    (memoryFrame_of_good originalRuntimeCode_feeMul_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_fee_mul) (by body_check Guest.guestFn_fee_mul) (by decide) (by decide) ?_
  refine aqgd_dec_lps _ _ _ (by decide) (by decide) ?_
  refine aqgd_dec_lps _ _ _ (by decide) (by decide) ?_
  refine aqgd_dec_lps _ _ _ (by decide) (by decide) ?_
  -- mgas = min(regular_budget, execution_gas), reservoir
  refine aqgd_decCall_lps _ _ _ _ _ _ _ originalRuntimeCode_min_lookup
    (memoryFrame_of_good originalRuntimeCode_min_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_min) (by body_check Guest.guestFn_min) (by decide) (by decide) ?_
  refine aqgd_dec_lps _ _ _ (by decide) (by decide) ?_
  exact hrest
#print axioms processTx_prefix_aqgdU
end pxu

section wru
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB k40 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo H0 Ts Bs U : BitVec 64} {M0 : Mem}

/-- The actual `increment_nonce(sender)` call keeping `PXR` (journal and key-buffer writes inside `Excl`). -/
theorem aqgd_call_incNonceU {LP : GA → Prop} (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
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
    (hx : ∀ L, LP L → ∃ X : BitVec 64, L.lookup (ofString "sender") = some (.val (.word X))) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) RR
      (.call (some (none,none)) (ofString "increment_nonce") [.var .local (ofString "sender")]) := by
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1, HeapIs G0' H1 ∧ DAPost n c T Out ko D B J C SKB H1 M0' M' G')
    _ _ _ _ _ originalRuntimeCode_incrementNonce_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,h01,reg,hn,_⟩
    refine aqgd_conseq (aqgd_jwsbu (incrementNonceT_aqgd (H0 := H1) (M0 := M0') (Nj := Nj) ne ne16 hAB hAo hBo hTs
      hBs hcA hcB hco hcd hc16 (le_trans p0 h01) jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe
      hOutSafe (hkoWs M0')) (keepsBo_of_installed originalRuntimeCode_incrementNonce_lookup (by decide)) (keepsWs_of_installed originalRuntimeCode_incrementNonce_lookup (by decide)))
      ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨ha,reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro F s values callee rs _ H _ ⟨lp,_⟩ _ args lookup
    obtain ⟨X,hX⟩ := hx _ lp
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hX] at args
    subst args
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_incrementNonce_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨X,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,h01,_,_,fr⟩ ⟨H1',hH',post⟩
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨lp,pxr_of_dapost hJE hSE h01 fr post⟩

/-- The actual `set_account_balance(sender, bal)` call keeping `PXR`. -/
theorem aqgd_call_setBalU {LP : GA → Prop} (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
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
    (hJE : ∀ x, InJ J C x → Excl x) (hSE : ∀ x, SkWin SKB x → Excl x) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) RR
      (.call (some (none,none)) (ofString "set_account_balance")
        [.var .local (ofString "sender"),.var .local (ofString "bal")]) := by
  refine aqgd_callSpecS (Vn' := fun x => x ≠ ofString "amount")
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ AmtL L) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1, HeapIs G0' H1 ∧ DAPost n c T Out ko D B J C SKB H1 M0' M' G')
    _ _ _ _ _ originalRuntimeCode_setAccountBalance_lookup (fun _ _ _ h => (setBal_callee h).1) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,H1,Nj,hH,h01,reg,hn,_⟩
    refine aqgd_conseq (aqgd_jwsbu (setAccountBalanceT_aqgd (H0 := H1) (M0 := M0') (Nj := Nj) ne ne16 hAB hAo hBo hTs
      hBs hcA hcB hco hcd hc16 (le_trans p0 h01) jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe
      hOutSafe (hkoWs M0')) (keepsBo_of_installed originalRuntimeCode_setAccountBalance_lookup (by decide)) (keepsWs_of_installed originalRuntimeCode_setAccountBalance_lookup (by decide)))
      ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨ha,reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro F s values callee rs _ H _ _ _ _ lookup
    exact ⟨⟨(setBal_callee lookup).2.2,(setBal_callee lookup).2.1⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,h01,_,_,fr⟩ ⟨H1',hH',post⟩
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨lp,pxr_of_dapost hJE hSE h01 fr post⟩

#print axioms aqgd_call_incNonceU
#print axioms aqgd_call_setBalU
end wru

section pwu
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd k16 kA kB k40 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo H0 Ts Bs U : BitVec 64} {M0 : Mem}

/-- The actual `process_transaction` body from the `increment_nonce(sender)` call through the sender balance
debit (`bal = u256_sub(...)` twice, `set_account_balance(sender, bal)`) to the `te_new()` declaration: every path
keeps `PXR` with the journal and key-buffer windows inside `Excl`. No callee frame hypotheses. -/
theorem processTx_writers_aqgdU {QM : Mem → GA → Prop} (Ix : BitVec 64) (ne : kd ≠ ko) (ne16 : k16 ≠ ko) (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
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
    (hrest : AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 34 (sourceFunctionBody Guest.guestFn_process_transaction))) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 28 (sourceFunctionBody Guest.guestFn_process_transaction)) := by
  unfold sourceFunctionBody at hrest ⊢
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq] at hrest ⊢
  simp only [Guest.guestFn_process_transaction,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,stateInitSpineDrop] at hrest ⊢
  refine aqgd_seq (aqgd_call_incNonceU ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE (fun _ lp => lp.2)) ?_
  refine aqgd_dec_lps _ _ _ (by decide) (by decide) ?_
  refine aqgd_seq (aqgd_u256Sub_lps _) ?_
  refine aqgd_seq (aqgd_u256Sub_lps _) ?_
  refine aqgd_seq (aqgd_call_setBalU ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE) ?_
  refine aqgd_seq aqgd_skip ?_
  exact hrest

#print axioms processTx_writers_aqgdU
/-- The actual `process_transaction` body from `bal_index = index + 1` (just after `state_fresh_tx()`) to the
`te_new()` declaration, composed from `processTx_prefix_aqgdU` and `processTx_writers_aqgdU`. Remaining temporary
scoped callee premises: `FrameC` for `encode_transaction`, `recover_sender_with_chain_id`, `check_transaction`,
`calculate_blob_gas_price`. -/
theorem processTx_to_teNew_aqgdU {QM : Mem → GA → Prop} (Ix Arr : BitVec 64)
    (fcEnc : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_encode_transaction))
    (fcRec : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_recover_sender_with_chain_id))
    (fcChk : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_check_transaction))
    (fcBgp : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_calculate_blob_gas_price))
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
    (hrest : AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 34 (sourceFunctionBody Guest.guestFn_process_transaction))) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_process_transaction)) :=
  processTx_prefix_aqgdU Ix Arr fcEnc fcRec fcChk fcBgp hBoD hBoO hBoE hArr hO0 hE0 hw0 hO8 hE8 hw8 hAB hAo hBo hTs hBs
    hcA hcB hOut hwP p0 K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs
    (processTx_writers_aqgdU Ix ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE hrest)

#print axioms processTx_to_teNew_aqgdU
/-- The actual `process_transaction` body from `bal_index = index + 1` to the `te_new()` declaration over the
pinned-workspace arena, with the `check_transaction` and `calculate_blob_gas_price` frame contracts discharged by
`checkTransaction_frameCU` and `blobGasPrice_frameCU`. Remaining callee premises: the `FrameCU` contracts of
`encode_transaction` and `recover_sender_with_chain_id`. -/
theorem processTx_to_teNew_final {QM : Mem → GA → Prop} (Ix Arr : BitVec 64)
    (fcEnc : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_encode_transaction))
    (fcRec : FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_recover_sender_with_chain_id))
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
    -- get_code inside check_transaction
    (ne40 : k40 ≠ ko) (hc40 : c k40 = Ts + 40#64)
    -- the u256_ws workspace written by calculate_blob_gas_price
    (hU : U.toNat + 640 ≤ 2 ^ 64) (hwWS : ¬ WS U w) (hWO : ∀ x, WS U x → Out x ∧ ∀ i, x ≠ c i)
    (hWE : ∀ x, WS U x → Excl x)
    (hrest : AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 34 (sourceFunctionBody Guest.guestFn_process_transaction))) :
    AQGD D B (JWSBU SP0 P0 FM G0 J C SKB Bo U) w (fun _ => False)
      (fun L M G => LPI Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_process_transaction))  :=
  have fcBgp := blobGasPrice_frameCU (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (J := J) (C := C) (SKB := SKB)
    (ko := ko) (D := D) (B := B) (T := T) hU hwWS hWO hWE
  processTx_to_teNew_aqgdU Ix Arr fcEnc fcRec
    (checkTransaction_frameCU fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs
      ne40 hc40 hwS hSO hSE)
    fcBgp hBoD hBoO hBoE hArr hO0 hE0 hw0 hO8 hE8 hw8 ne ne16 hAB hAo hBo hTs hBs hcA hcB hco hcd hc16 p0 jfit hwJ
    hwP hOut hwS hJO hSO jsep K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs hJE hSE hrest

#print axioms processTx_to_teNew_final
end pwu
end InitECandidate.Runtime
