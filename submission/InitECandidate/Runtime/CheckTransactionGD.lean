import InitECandidate.Runtime.ProcessTxWritersGD
import InitECandidate.Runtime.OriginalTxCheckCalleesCode
import InitECandidate.Runtime.OriginalMemeqCode
/-!
Frame contract of the actual `check_transaction` over the content-carrying registry: callee-entry facts from
lookup success (`callee_one`, `callee_two`), locals-free step rules, `CX`-keeping wrappers for `get_account`,
`get_code` and frame-contract callees (heap lower bound taken from the arena), the body split into spine chunks
(`ckK0` … `ckK28`, tied to the source by `checkTransaction_body_eq`), and `checkTransaction_frameC`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Callee entry of a one-word-parameter function: the parameter is bound to a word. -/
theorem callee_one {f p : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(p,.one)],bd,rs0)) {values : List (ValueHOL 64)}
    {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    ∃ A : BitVec 64, callee.lookup p = some (.val (.word A)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i b0 cl rs1 found
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨_,hc,_⟩ := h
    have hl : callee.lookup = cl := by rw [← hc]
    clear hc
    unfold Flapjack.lookupCodeHOLExact at found
    rw [inst] at found
    dsimp only at found
    split at found
    · rename_i cond
      obtain ⟨_,hlen,hall⟩ := cond
      simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨_,hcl,_⟩ := found
      match values, hlen, hall with
      | [v0], _, hall =>
        simp only [List.zip_cons_cons,List.zip_nil_right,List.all_cons,List.all_nil,Bool.and_true] at hall
        obtain ⟨a,rfl⟩ : ∃ a : BitVec 64, v0 = .val (.word a) := scalar_of_shape hall
        subst hcl
        exact ⟨a,by rw [hl]; simp⟩
    · cases found

/-- Callee entry of a two-word-parameter function: both parameters are bound to words. -/
theorem callee_two {f p q : MlS} {bd : ProgHOL 64} {rs0 : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some ([(p,.one),(q,.one)],bd,rs0)) (ne : p ≠ q)
    {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : GA} {rs : ShapeHOL}
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite originalRuntimeCode.lookup f values = some (body,callee,rs)) :
    ∃ A B : BitVec 64, callee.lookup p = some (.val (.word A)) ∧ callee.lookup q = some (.val (.word B)) := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i b0 cl rs1 found
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨_,hc,_⟩ := h
    have hl : callee.lookup = cl := by rw [← hc]
    clear hc
    unfold Flapjack.lookupCodeHOLExact at found
    rw [inst] at found
    dsimp only at found
    split at found
    · rename_i cond
      obtain ⟨_,hlen,hall⟩ := cond
      simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨_,hcl,_⟩ := found
      match values, hlen, hall with
      | [v0,v1], _, hall =>
        simp only [List.zip_cons_cons,List.zip_nil_right,List.all_cons,List.all_nil,Bool.and_true,
          Bool.and_eq_true] at hall
        obtain ⟨s0,s1⟩ := hall
        obtain ⟨a,rfl⟩ : ∃ a : BitVec 64, v0 = .val (.word a) := scalar_of_shape s0
        obtain ⟨b,rfl⟩ : ∃ b : BitVec 64, v1 = .val (.word b) := scalar_of_shape s1
        subst hcl
        exact ⟨a,b,by rw [hl]; simp [ne],by rw [hl]; simp⟩
    · cases found

#print axioms callee_one
#print axioms callee_two
section gen
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A body with no normal fall-through, proved over no scalar locals, holds for any scalar-locals set and any normal
postcondition. -/
theorem aqgd_noFall {Vn : MlS → Prop} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64}
    (h : AQGD D B A w (fun _ => False) P (fun _ _ _ => False) RR p) : AQGD D B A w Vn P Q RR p := by
  intro F s code dom aw _ H hH pre
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom aw (fun _ h => h.elim) H hH pre
  exact ⟨m,a,fun e => (n e).2.choose_spec.2.elim,r,c,b⟩

variable {X Q : Mem → GA → Prop}

theorem aqgd_dec_x (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (hb : AQGD D B A w (fun _ => False) (fun _ M G => X M G) (fun _ M G => Q M G) RR body) :
    AQGD D B A w (fun _ => False) (fun _ M G => X M G) (fun _ M G => Q M G) RR (.dec name shape init body) :=
  aqgd_dec _ _ _ (fun h => h.elim) (fun _ _ _ _ _ pre _ _ _ => pre) hb (fun _ _ _ _ _ _ _ h => h)

theorem aqgd_decCall_x (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (hb : AQGD D B A w (fun _ => False) (fun _ M G => X M G) (fun _ M G => Q M G) RR cont) :
    AQGD D B A w (fun _ => False) (fun _ M G => X M G) (fun _ M G => Q M G) RR
      (.decCall name shape function arguments cont) :=
  aqgd_decCall_mfF _ _ _ _ _ _ _ installed mf nb nc (fun _ _ _ _ pre => pre) hb (fun _ _ _ _ _ _ _ h => h)

theorem aqgd_assign_x (x : MlS) (e : ExpHOL 64) :
    AQGD D B A w (fun _ => False) (fun _ M G => X M G) (fun _ M G => X M G) RR (.assign .local x e) :=
  aqgd_assignLocal _ _ (fun _ _ _ _ pre _ _ => pre)

theorem aqgd_callAssign_x (name function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true) :
    AQGD D B A w (fun _ => False) (fun _ M G => X M G) (fun _ M G => X M G) RR
      (.call (some (some (.local,name),none)) function arguments) :=
  aqgd_callAssignFS (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    _ _ _ _ _ _ installed (fun _ _ _ _ _ h => h.elim) (fun h => h)
    (fun _ M0' G0' _ => aqgd_of_mf mf nb nc M0' G0') (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun _ _ _ _ _ _ pre ⟨e1,e2⟩ => by rw [e1,e2]; exact pre)

/-- A loop whose body keeps a locals-free invariant (no `break` reaching the loop). -/
theorem aqgd_while_x (c : ExpHOL 64) {body : ProgHOL 64}
    (hb : AQGD D B A w (fun _ => False) (fun _ M G => X M G) (fun _ M G => X M G) RR body) :
    AQGD D B A w (fun _ => False) (fun _ M G => X M G) (fun _ M G => X M G) RR (.while c body) :=
  aqgd_conseq (aqgd_whileBreak (C := fun _ _ _ => True) (Qb := fun _ _ _ => False) _
      (fun _ _ _ _ _ _ _ _ => trivial)
      (aqgb_of_aqgd (aqgd_conseq hb (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))))
    (fun _ _ _ h => h) (fun _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h)

/-- A fact following from the arena predicate and the precondition may be assumed when building the triple. -/
theorem aqgd_of_arenaFact {Vn : MlS → Prop} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64} {Φ : Prop}
    (hΦ : ∀ L M g, A g → P L M g → Φ) (h : Φ → AQGD D B A w Vn P Q RR p) : AQGD D B A w Vn P Q RR p := by
  intro F s code dom aw sl H hH pre
  unfold GIs at hH; subst hH
  exact h (hΦ _ _ _ aw pre) F s code dom aw sl _ rfl pre

#print axioms aqgd_noFall
#print axioms aqgd_callAssign_x
#print axioms aqgd_while_x
end gen

/-- The `check_transaction` frame invariant: the content-carrying registry at a heap pointer not below `H0`, the
journal counter `Nj`, and every outside word outside `Excl` equal to the entry memory `M0`. This is exactly the
return condition of `FrameC`. -/
def CX (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (Excl : BitVec 64 → Prop) (H0 Nj : BitVec 64) (M0 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ H', HeapIs G H' ∧ H0.toNat ≤ H'.toNat ∧ RegT n c T Out H' M D B ko ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ Excl x → M x = M0 x

theorem jws_heap_lo {SP0 P0 FM J C SKB H : BitVec 64} {G0 g : GA} (h : JWS SP0 P0 FM G0 J C SKB g)
    (hH : HeapIs g H) : P0.toNat ≤ H.toNat := by
  obtain ⟨⟨⟨_,_,⟨h',hh,lo,_,_⟩,_⟩,_⟩,_⟩ := h
  unfold HeapIs at hH; rw [hh] at hH
  simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at hH
  subst hH; exact lo

section cx
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB k40 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB H0 Nj Ts Bs : BitVec 64} {M0 : Mem} {Q : Mem → GA → Prop}

/-- A declared call to a callee with a frame contract, keeping `CX`. -/
theorem aqgd_decCall_fcX (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (fc : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl body)
    (hcont : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
      (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ M G => Q M G) RR cont) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
      (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ M G => Q M G) RR
      (.decCall name shape function arguments cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1 : BitVec 64, HeapIs G0' H1 ∧
        ∃ H', HeapIs G' H' ∧ H1.toNat ≤ H'.toNat ∧ RegT n c T Out H' M' D B ko ∧
          G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ Excl x → M' x = M0' x)
    (Pc := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (Qc := fun _ M G => Q M G)
    _ _ _ _ _ _ _ installed allOne ?_ (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim) ?_ hcont
    (fun _ _ _ _ _ _ _ h => h)
  · intro L0 M0' G0' ⟨H1,hH,_,reg,hn,_⟩
    refine aqgd_conseq (fc H1 Nj M0') ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hM,hG⟩
      subst hM hG
      exact ⟨reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro L M G v M' G' ⟨H1,hH,hle,_,_,fr⟩ ⟨H1',hH',H',hH2,hle',reg',hn',fr'⟩ _
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨H',hH2,le_trans hle hle',reg',hn',fun x ho hx => (fr' x ho hx).trans (fr x ho hx)⟩

set_option maxHeartbeats 16000000 in
/-- The actual `get_account(x)` declared call keeping `CX`. -/
theorem aqgd_decCall_getAccountX (name : MlS) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hOut : Out w) (hwP : w.toNat < P0.toNat) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (hcont : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
      (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ M G => Q M G) RR cont) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
      (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ M G => Q M G) RR
      (.decCall name .one (ofString "get_account") arguments cont) := by
  refine aqgd_decCallSpec (Vn' := fun _ => True)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ (H1 : BitVec 64) (l : Fin n → TLay), HeapIs G0' H1 ∧
        RegPure n c T Out H1 l ∧ RegMem n c T l M0' ∧ TCont D B M0' (T ko) (l ko) ∧
        (∀ x, (l ko).arr x → x.toNat < H1.toNat) ∧
        (G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H', HeapIs G' H' ∧
          ((Reg n c T Out H' M' ∧ H1.toNat ≤ H'.toNat) ∧
            ∀ x, GaKeep SP0 P0 FM K Pd NB Out (T ko) (l ko) x → M' x = M0' x)))
    (Pc := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (Qc := fun _ M G => Q M G)
    _ _ _ _ _ _ _ originalRuntimeCode_account_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hcont
    (fun _ _ _ _ _ _ _ h => h)
  · intro L0 M0' G0' ⟨H1,hH,h01,⟨l,pure,mem,tc,ab⟩,hn,_⟩
    refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H1.toNat) (fun L M g aw ⟨_,_,hg⟩ => jws_heap_lo aw (hg ▸ hH)) ?_
    intro p1
    refine aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_withA (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_account_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (accountRegT_aqmh n c T kA kB ko hAB hAo hBo Ts Bs hTs hBs hcA hcB Out hOut H1 p1 K Pd NB hK0 hPd0 hNB0
        safe (hOutSafe w hOut).1 hwP l pure M0' mem ab))))
      (keepsSkBuf_of_installed originalRuntimeCode_account_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨hn,H1,hH,⟨ha,rfl,l,reg_of pure mem,pure.2.1,pure.2.2⟩,rfl⟩
    · intro v M' G' ⟨post,_⟩
      exact ⟨H1,l,hH,pure,mem,tc,ab,post⟩
  · intro F s values callee rs _ H _ _ _ _ lookup
    exact ⟨callee_one originalRuntimeCode_account_lookup lookup,rfl,rfl⟩
  · intro L M G v M' G' ⟨H1,hH,hle,_,_,fr⟩ ⟨H1',l,hH',pure,mem,tc,ab,hn',H',hH2,⟨reg,hle'⟩,frG⟩ _
    have e := heapIs_unique hH hH'
    subst e
    have keepT : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
        M' x = M x := fun x hx => frG x (Or.inl ⟨hx,hkoWs M (l ko) (mem ko).2 x hx⟩)
    exact ⟨H',hH2,le_trans hle hle',regT_of_reg l pure tc ab reg hle' keepT,hn',
      fun x ho hxe => (frG x (Or.inr ⟨ho,hOutSafe x ho⟩)).trans (fr x ho hxe)⟩

set_option maxHeartbeats 16000000 in
/-- The actual `get_code(code_hash, addr)` declared call keeping `CX` (key-buffer writes inside `Excl`). -/
theorem aqgd_decCall_getCodeX (name : MlS) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (ne : k40 ≠ ko) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hc40 : c k40 = Ts + 40#64) (hwP : w.toNat < P0.toNat) (hOut : Out w)
    (hwS : ¬ SkWin SKB w) (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSE : ∀ x, SkWin SKB x → Excl x)
    (hcont : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
      (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ M G => Q M G) RR cont) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
      (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ M G => Q M G) RR
      (.decCall name (.comb [.one,.one]) (ofString "get_code") arguments cont) := by
  refine aqgd_decCallSpec (Vn' := fun x => x ≠ ofString "w" ∧ x ≠ ofString "c")
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (L : GA) (M : Mem) (G : GA) =>
      ((∃ Ch : BitVec 64, L.lookup (ofString "code_hash") = some (.val (.word Ch))) ∧
        (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A)))) ∧ M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) =>
      ∃ H1 : BitVec 64, HeapIs G0' H1 ∧ GCPost n c T Out ko D B SKB H1 Nj M0' M' G')
    (Pc := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (Qc := fun _ M G => Q M G)
    _ _ _ _ _ _ _ originalRuntimeCode_getCode_lookup (by simp) ?_ ?_ (fun h => h.elim) ?_ hcont
    (fun _ _ _ _ _ _ _ h => h)
  · intro L0 M0' G0' ⟨H1,hH,h01,reg,hn,_⟩
    refine aqgd_of_arenaFact (Φ := P0.toNat ≤ H1.toNat) (fun L M g aw ⟨_,_,hg⟩ => jws_heap_lo aw (hg ▸ hH)) ?_
    intro p1
    refine aqgd_conseq (getCodeT_aqgd (T := T) (H0 := H1) (M0 := M0') (Nj := Nj) ne hTs hc40 p1 hwP hOut hwS
      hSO) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨ha,hM,hG⟩
      subst hM hG
      exact ⟨ha,reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,hH,post⟩
  · intro F s values callee rs _ H _ _ _ _ lookup
    obtain ⟨Ch,A,h1,h2⟩ := callee_two originalRuntimeCode_getCode_lookup (by decide) lookup
    exact ⟨⟨⟨Ch,h1⟩,⟨A,h2⟩⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨H1,hH,hle,_,_,fr⟩ ⟨H1',hH',H',hH2,hle',reg',hn',fr'⟩ _
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨H',hH2,le_trans hle hle',reg',hn',fun x ho hx => (fr' x ho (fun k => hx (hSE x k))).trans (fr x ho hx)⟩

#print axioms aqgd_decCall_fcX
#print axioms aqgd_decCall_getAccountX
#print axioms aqgd_decCall_getCodeX
end cx
/-- Left part of a sequence. -/
def seqHead : ProgHOL 64 → ProgHOL 64
  | .seq a _ => a
  | p => p
/-- Branches of a conditional. -/
def iteThen : ProgHOL 64 → ProgHOL 64
  | .ite _ y _ => y
  | p => p
def iteElse : ProgHOL 64 → ProgHOL 64
  | .ite _ _ n => n
  | p => p


/-- `check_transaction` body from spine position 28. -/
def ckK28 : ProgHOL 64 :=
  ProgHOL.decCall (ofString "need") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_add_carry") [ExpHOL.var VarKind.local (ofString "max_gas_fee"), ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 160#64])] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.rfield 4 (ExpHOL.var VarKind.local (ofString "need"))) (ExpHOL.const 0#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 93#64)) ProgHOL.skip) (ProgHOL.decCall (ofString "lt5") ShapeHOL.one (ofString "u256_lt") [ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "acct"), ExpHOL.const 8#64]), ExpHOL.rstruct [ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "need")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "need")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "need")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "need"))]] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "lt5")) (ExpHOL.const 0#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 93#64)) ProgHOL.skip) (ProgHOL.decCall (ofString "scode") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one]) (ofString "get_code") [ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "acct"), ExpHOL.const 48#64]), ExpHOL.var VarKind.local (ofString "sender")] (ProgHOL.decCall (ofString "che") ShapeHOL.one (ofString "memeq") [ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "acct"), ExpHOL.const 48#64]), ExpHOL.var VarKind.global (ofString "empty_code_hash"), ExpHOL.const 32#64] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "che")) (ExpHOL.const 0#64)) (ProgHOL.decCall (ofString "vd") ShapeHOL.one (ofString "is_valid_delegation") [ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "scode")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "scode"))] (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "vd")) (ExpHOL.const 0#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 94#64)) ProgHOL.skip)) ProgHOL.skip) (ProgHOL.return (ExpHOL.var VarKind.local (ofString "price")))))))))

/-- `check_transaction` body from spine position 20. -/
def ckK20 : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "ty")) (ExpHOL.const 4#64)) (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 280#64])) (ExpHOL.const 0#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 90#64)) ProgHOL.skip) ProgHOL.skip) (ProgHOL.dec (ofString "tn") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 16#64])) (ProgHOL.decCall (ofString "fits") ShapeHOL.one (ofString "u256_fits_word") [ExpHOL.var VarKind.local (ofString "tn")] (ProgHOL.dec (ofString "an") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "acct"), ExpHOL.const 0#64])) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "fits")) (ExpHOL.const 0#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 92#64)) ProgHOL.skip) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "tn"))) (ExpHOL.var VarKind.local (ofString "an"))) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 91#64)) ProgHOL.skip) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "an")) (ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "tn")))) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 92#64)) ProgHOL.skip) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "ovf")) (ExpHOL.const 0#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 93#64)) ProgHOL.skip) (ckK28))))))))

/-- `check_transaction` body from spine position 19. -/
def ckK19 : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "ty")) (ExpHOL.const 3#64)) (ProgHOL.dec (ofString "nb") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 264#64])) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "nb")) (ExpHOL.const 0#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 86#64)) ProgHOL.skip) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.const 6#64) (ExpHOL.var VarKind.local (ofString "nb"))) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 87#64)) ProgHOL.skip) (ProgHOL.dec (ofString "j") ShapeHOL.one (ExpHOL.const 0#64) (ProgHOL.seq (ProgHOL.while (ExpHOL.cmp Cmp.less (ExpHOL.var VarKind.local (ofString "j")) (ExpHOL.var VarKind.local (ofString "nb"))) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.loadByte (ExpHOL.op BinOp.add [ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 256#64]), ExpHOL.panop PanOp.mul [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 32#64]])) (ExpHOL.const 1#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 88#64)) ProgHOL.skip) (ProgHOL.assign VarKind.local (ofString "j") (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "j"), ExpHOL.const 1#64])))) (ProgHOL.decCall (ofString "bgp") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "calculate_blob_gas_price") [ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "be"), ExpHOL.const 96#64])] (ProgHOL.dec (ofString "mfb") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 224#64])) (ProgHOL.decCall (ofString "lt4") ShapeHOL.one (ofString "u256_lt") [ExpHOL.var VarKind.local (ofString "mfb"), ExpHOL.var VarKind.local (ofString "bgp")] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "lt4")) (ExpHOL.const 0#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 89#64)) ProgHOL.skip) (ProgHOL.decCall (ofString "bf") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "fee_mul") [ExpHOL.var VarKind.local (ofString "tx_blob_gas"), ExpHOL.var VarKind.local (ofString "mfb")] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "bf"))) (ExpHOL.const 0#64)) (ProgHOL.assign VarKind.local (ofString "ovf") (ExpHOL.const 1#64)) ProgHOL.skip) (ProgHOL.decCall (ofString "sum") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_add_carry") [ExpHOL.var VarKind.local (ofString "max_gas_fee"), ExpHOL.rstruct [ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "bf")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "bf")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "bf")), ExpHOL.rfield 4 (ExpHOL.var VarKind.local (ofString "bf"))]] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.rfield 4 (ExpHOL.var VarKind.local (ofString "sum"))) (ExpHOL.const 0#64)) (ProgHOL.assign VarKind.local (ofString "ovf") (ExpHOL.const 1#64)) ProgHOL.skip) (ProgHOL.assign VarKind.local (ofString "max_gas_fee") (ExpHOL.rstruct [ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "sum")), ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "sum")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "sum")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "sum"))]))))))))))))))) ProgHOL.skip) (ckK20)

/-- `check_transaction` body from spine position 16. -/
def ckK16 : ProgHOL 64 :=
  ProgHOL.decCall (ofString "mgf") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "fee_mul") [ExpHOL.var VarKind.local (ofString "gas"), ExpHOL.var VarKind.local (ofString "max_fee_per_gas")] (ProgHOL.dec (ofString "ovf") ShapeHOL.one (ExpHOL.rfield 0 (ExpHOL.var VarKind.local (ofString "mgf"))) (ProgHOL.dec (ofString "max_gas_fee") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.rstruct [ExpHOL.rfield 1 (ExpHOL.var VarKind.local (ofString "mgf")), ExpHOL.rfield 2 (ExpHOL.var VarKind.local (ofString "mgf")), ExpHOL.rfield 3 (ExpHOL.var VarKind.local (ofString "mgf")), ExpHOL.rfield 4 (ExpHOL.var VarKind.local (ofString "mgf"))]) (ckK19)))

/-- `check_transaction` body from spine position 15. -/
def ckK15 : ProgHOL 64 :=
  ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.const 0#64) (ExpHOL.op BinOp.or [ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "ty")) (ExpHOL.const 0#64), ExpHOL.cmp Cmp.equal (ExpHOL.var VarKind.local (ofString "ty")) (ExpHOL.const 1#64)])) (ProgHOL.dec (ofString "gp") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 48#64])) (ProgHOL.decCall (ofString "lt") ShapeHOL.one (ofString "u256_lt") [ExpHOL.var VarKind.local (ofString "gp"), ExpHOL.var VarKind.local (ofString "base_fee")] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "lt")) (ExpHOL.const 0#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 83#64)) ProgHOL.skip) (ProgHOL.seq (ProgHOL.assign VarKind.local (ofString "price") (ExpHOL.var VarKind.local (ofString "gp"))) (ProgHOL.assign VarKind.local (ofString "max_fee_per_gas") (ExpHOL.var VarKind.local (ofString "gp"))))))) (ProgHOL.dec (ofString "mf") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 112#64])) (ProgHOL.dec (ofString "mp") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 80#64])) (ProgHOL.decCall (ofString "lt1") ShapeHOL.one (ofString "u256_lt") [ExpHOL.var VarKind.local (ofString "mf"), ExpHOL.var VarKind.local (ofString "mp")] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "lt1")) (ExpHOL.const 0#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 84#64)) ProgHOL.skip) (ProgHOL.decCall (ofString "lt2") ShapeHOL.one (ofString "u256_lt") [ExpHOL.var VarKind.local (ofString "mf"), ExpHOL.var VarKind.local (ofString "base_fee")] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "lt2")) (ExpHOL.const 0#64)) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 85#64)) ProgHOL.skip) (ProgHOL.decCall (ofString "diff") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ofString "u256_sub") [ExpHOL.var VarKind.local (ofString "mf"), ExpHOL.var VarKind.local (ofString "base_fee")] (ProgHOL.decCall (ofString "lt3") ShapeHOL.one (ofString "u256_lt") [ExpHOL.var VarKind.local (ofString "mp"), ExpHOL.var VarKind.local (ofString "diff")] (ProgHOL.dec (ofString "prio") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.var VarKind.local (ofString "diff")) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.notEqual (ExpHOL.var VarKind.local (ofString "lt3")) (ExpHOL.const 0#64)) (ProgHOL.assign VarKind.local (ofString "prio") (ExpHOL.var VarKind.local (ofString "mp"))) ProgHOL.skip) (ProgHOL.seq (ProgHOL.call (some (some (VarKind.local, ofString "price"), none)) (ofString "u256_add") [ExpHOL.var VarKind.local (ofString "prio"), ExpHOL.var VarKind.local (ofString "base_fee")]) (ProgHOL.assign VarKind.local (ofString "max_fee_per_gas") (ExpHOL.var VarKind.local (ofString "mf"))))))))))))))) (ckK16)

/-- `check_transaction` body from spine position 10. -/
def ckK10 : ProgHOL 64 :=
  ProgHOL.decCall (ofString "acct") ShapeHOL.one (ofString "get_account") [ExpHOL.var VarKind.local (ofString "sender")] (ProgHOL.dec (ofString "base_fee") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.load (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "be"), ExpHOL.const 48#64])) (ProgHOL.dec (ofString "price") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.rstruct [ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64]) (ProgHOL.dec (ofString "max_fee_per_gas") (ShapeHOL.comb [ShapeHOL.one, ShapeHOL.one, ShapeHOL.one, ShapeHOL.one]) (ExpHOL.rstruct [ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64, ExpHOL.const 0#64]) (ProgHOL.dec (ofString "ty") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 0#64])) (ckK15)))))

/-- `check_transaction` body from spine position 0. -/
def ckK0 : ProgHOL 64 :=
  ProgHOL.dec (ofString "block_gas_limit") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "be"), ExpHOL.const 8#64])) (ProgHOL.dec (ofString "regular_avail") ShapeHOL.one (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "block_gas_limit"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "bo"), ExpHOL.const 0#64])]) (ProgHOL.dec (ofString "state_avail") ShapeHOL.one (ExpHOL.op BinOp.sub [ExpHOL.var VarKind.local (ofString "block_gas_limit"), ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "bo"), ExpHOL.const 8#64])]) (ProgHOL.dec (ofString "blob_avail") ShapeHOL.one (ExpHOL.op BinOp.sub [ExpHOL.const 2752512#64, ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.global (ofString "bo"), ExpHOL.const 48#64])]) (ProgHOL.dec (ofString "gas") ShapeHOL.one (ExpHOL.load ShapeHOL.one (ExpHOL.op BinOp.add [ExpHOL.var VarKind.local (ofString "tx"), ExpHOL.const 144#64])) (ProgHOL.decCall (ofString "capped") ShapeHOL.one (ofString "min") [ExpHOL.const 16777216#64, ExpHOL.var VarKind.local (ofString "gas")] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "regular_avail")) (ExpHOL.var VarKind.local (ofString "capped"))) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 80#64)) ProgHOL.skip) (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "state_avail")) (ExpHOL.var VarKind.local (ofString "gas"))) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 81#64)) ProgHOL.skip) (ProgHOL.decCall (ofString "tx_blob_gas") ShapeHOL.one (ofString "calculate_total_blob_gas") [ExpHOL.var VarKind.local (ofString "tx")] (ProgHOL.seq (ProgHOL.ite (ExpHOL.cmp Cmp.lower (ExpHOL.var VarKind.local (ofString "blob_avail")) (ExpHOL.var VarKind.local (ofString "tx_blob_gas"))) (ProgHOL.raise (ofString "BlockErr") (ExpHOL.const 82#64)) ProgHOL.skip) (ckK10))))))))))

section ck
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB k40 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Ts Bs H0 Nj : BitVec 64} {M0 : Mem}
  (fcBgp : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_calculate_blob_gas_price))
  (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
  (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
  (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
  (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hOut : Out w) (hwP : w.toNat < P0.toNat) (K Pd NB : BitVec 64)
  (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
  (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
  (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
  (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
  (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
  (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
    ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
  (ne40 : k40 ≠ ko) (hc40 : c k40 = Ts + 40#64) (hwS : ¬ SkWin SKB w)
  (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSE : ∀ x, SkWin SKB x → Excl x)
include fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 28. -/
theorem lk28 : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK28 := by
  unfold ckK28
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256AddCarry_lookup (memoryFrame_of_good originalRuntimeCode_u256AddCarry_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_add_carry) (by body_check Guest.guestFn_u256_add_carry) ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_decCall_getCodeX _ _ ne40 hTs hc40 hwP hOut hwS hSO hSE ?_
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_memeq_lookup (memoryFrame_of_good originalRuntimeCode_memeq_lookup (by decide) (by decide)) (by body_check Guest.guestFn_memeq) (by body_check Guest.guestFn_memeq) ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_isValidDelegation_lookup (memoryFrame_of_good originalRuntimeCode_isValidDelegation_lookup (by decide) (by decide)) (by body_check Guest.guestFn_is_valid_delegation) (by body_check Guest.guestFn_is_valid_delegation) ?_
      refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
      · exact aqgd_raise _ _
      · exact aqgd_skip
    · exact aqgd_skip
  exact aqgd_return _ (fun _ _ _ _ _ h _ _ => h)

/-- Frame of `check_transaction` from spine position 20. -/
theorem lk20 : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK20 := by
  unfold ckK20
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
      · exact aqgd_raise _ _
      · exact aqgd_skip
    · exact aqgd_skip
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256FitsWord_lookup (memoryFrame_of_good originalRuntimeCode_u256FitsWord_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_fits_word) (by body_check Guest.guestFn_u256_fits_word) ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  exact lk28 fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 19. -/
theorem lk19 : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK19 := by
  unfold ckK19
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · refine aqgd_dec_x _ _ _ ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_dec_x _ _ _ ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_while_x _ ?_
        refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
        · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
          · exact aqgd_raise _ _
          · exact aqgd_skip
        exact aqgd_assign_x _ _
      refine aqgd_decCall_fcX _ _ _ _ _ _ _ originalRuntimeCode_blobGasPrice_lookup (by simp) fcBgp ?_
      refine aqgd_dec_x _ _ _ ?_
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_feeMul_lookup (memoryFrame_of_good originalRuntimeCode_feeMul_lookup (by decide) (by decide)) (by body_check Guest.guestFn_fee_mul) (by body_check Guest.guestFn_fee_mul) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_assign_x _ _
        · exact aqgd_skip
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256AddCarry_lookup (memoryFrame_of_good originalRuntimeCode_u256AddCarry_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_add_carry) (by body_check Guest.guestFn_u256_add_carry) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_assign_x _ _
        · exact aqgd_skip
      exact aqgd_assign_x _ _
    · exact aqgd_skip
  exact lk20 fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 16. -/
theorem lk16 : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK16 := by
  unfold ckK16
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_feeMul_lookup (memoryFrame_of_good originalRuntimeCode_feeMul_lookup (by decide) (by decide)) (by body_check Guest.guestFn_fee_mul) (by body_check Guest.guestFn_fee_mul) ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  exact lk19 fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 15. -/
theorem lk15 : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK15 := by
  unfold ckK15
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · refine aqgd_dec_x _ _ _ ?_
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · exact aqgd_assign_x _ _
      exact aqgd_assign_x _ _
    · refine aqgd_dec_x _ _ _ ?_
      refine aqgd_dec_x _ _ _ ?_
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_raise _ _
        · exact aqgd_skip
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Sub_lookup (memoryFrame_of_good originalRuntimeCode_u256Sub_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_sub) (by body_check Guest.guestFn_u256_sub) ?_
      refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_u256Lt_lookup (memoryFrame_of_good originalRuntimeCode_u256Lt_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_lt) (by body_check Guest.guestFn_u256_lt) ?_
      refine aqgd_dec_x _ _ _ ?_
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
        · exact aqgd_assign_x _ _
        · exact aqgd_skip
      refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
      · exact aqgd_callAssign_x _ _ _ _ _ _ originalRuntimeCode_u256Add_lookup (memoryFrame_of_good originalRuntimeCode_u256Add_lookup (by decide) (by decide)) (by body_check Guest.guestFn_u256_add) (by body_check Guest.guestFn_u256_add)
      exact aqgd_assign_x _ _
  exact lk16 fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 10. -/
theorem lk10 : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK10 := by
  unfold ckK10
  refine aqgd_decCall_getAccountX _ _ hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  exact lk15 fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

/-- Frame of `check_transaction` from spine position 0. -/
theorem lk0 : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => False)
    (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) (fun _ _ _ => False) (fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ckK0 := by
  unfold ckK0
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_dec_x _ _ _ ?_
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_min_lookup (memoryFrame_of_good originalRuntimeCode_min_lookup (by decide) (by decide)) (by body_check Guest.guestFn_min) (by body_check Guest.guestFn_min) ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  refine aqgd_decCall_x _ _ _ _ _ _ _ originalRuntimeCode_totalBlobGas_lookup (memoryFrame_of_good originalRuntimeCode_totalBlobGas_lookup (by decide) (by decide)) (by body_check Guest.guestFn_calculate_total_blob_gas) (by body_check Guest.guestFn_calculate_total_blob_gas) ?_
  refine aqgd_seq (Q := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ ?_
  · refine aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _ (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)) (aqgd_conseq (P := fun _ M G => CX n c T Out ko D B Excl H0 Nj M0 M G) ?_ (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))
    · exact aqgd_raise _ _
    · exact aqgd_skip
  exact lk10 fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE

end ck

/-- The actual `check_transaction` body is the chunked term. -/
theorem checkTransaction_body_eq : sourceFunctionBody Guest.guestFn_check_transaction = ckK0 := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_check_transaction,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_some]
  rfl

#print axioms checkTransaction_body_eq

section fin
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64}
  {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB k40 : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Ts Bs : BitVec 64}

/-- Frame contract of the actual `check_transaction(tx, sender)`: from the content-carrying registry at any entry
heap, every return keeps the registry at the exit heap, the journal counter, and every outside word outside `Excl`
(the key buffer `SkWin SKB` lies in `Excl`). Real specs: `get_account`, `get_code`, and the read-only callees `min`,
`calculate_total_blob_gas`, `u256_lt`, `u256_sub`, `u256_add`, `u256_add_carry`, `fee_mul`, `u256_fits_word`,
`memeq`, `is_valid_delegation` (whole-program memory/globals decisions). Remaining temporary premise: the
`calculate_blob_gas_price` frame contract `fcBgp`. -/
theorem checkTransaction_frameC
    (fcBgp : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_calculate_blob_gas_price))
    (hAB : kA ≠ kB) (hAo : kA ≠ ko) (hBo : kB ≠ ko)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (hOut : Out w) (hwP : w.toNat < P0.toNat) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) →
      ∀ x, InTabF (T ko) lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x)
    (ne40 : k40 ≠ ko) (hc40 : c k40 = Ts + 40#64) (hwS : ¬ SkWin SKB w)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i) (hSE : ∀ x, SkWin SKB x → Excl x) :
    FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_check_transaction) := by
  intro H0 Nj M0
  rw [checkTransaction_body_eq]
  exact aqgd_noFall (aqgd_conseq (lk0 (H0 := H0) (Nj := Nj) (M0 := M0) fcBgp hAB hAo hBo hTs hBs hcA hcB hOut hwP
      K Pd NB hK0 hPd0 hNB0 safe hOutSafe hkoWs ne40 hc40 hwS hSO hSE)
    (fun _ M G ⟨reg,hM,hH,hn⟩ => ⟨H0,hH,le_refl _,reg,hn,fun x _ _ => by rw [hM]⟩)
    (fun _ _ _ h => h) (fun _ _ _ h => h))

#print axioms checkTransaction_frameC
end fin
end InitECandidate.Runtime
