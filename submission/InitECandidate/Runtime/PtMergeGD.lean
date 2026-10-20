import InitECandidate.Runtime.DestroyStorageGD
import InitECandidate.Runtime.HtabUnionInto
import InitECandidate.Runtime.OriginalPtSufCode
import InitECandidate.Runtime.DivmnuWindowGD
import InitECandidate.Runtime.DigitsDivmodGD
/-!
The actual `htab_union_into(dst, src)` into a registry table `dst = T kt` (`kt ≠ ko`) from any source pointer: the
source's count and items are read only (`htab_item` is a memory frame); every used item is inserted by the original
`htab_set` on the registry table (`set_aqmh` at the arena bound raised to the current heap pointer, then `regT_set`).
The registry with content is re-established at the exit heap pointer and every outside word is kept.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Locals of `htab_union_into`: `dst = Td`, a word `src`. -/
def UL (Td : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "dst") = some (.val (.word Td)) ∧ ∃ S : BitVec 64, L.lookup (ofString "src") = some (.val (.word S))

theorem ul_upd {Td : BitVec 64} {L : GA} (h : UL Td L) (x : MlS) (v : ValueHOL 64) (h1 : ofString "dst" ≠ x)
    (h2 : ofString "src" ≠ x) : UL Td (L.update (x,v)) :=
  ⟨by rw [lookup_update_ne' _ _ h1]; exact h.1,let ⟨S,hS⟩ := h.2; ⟨S,by rw [lookup_update_ne' _ _ h2]; exact hS⟩⟩

theorem ul_res {Td : BitVec 64} {L : GA} (h : UL Td L) (x : MlS) (o : Option (ValueHOL 64)) (h1 : ofString "dst" ≠ x)
    (h2 : ofString "src" ≠ x) : UL Td (L.resVarEq (x,o)) :=
  ⟨by rw [resVar_lookup_ne _ _ _ _ h1]; exact h.1,let ⟨S,hS⟩ := h.2; ⟨S,by rw [resVar_lookup_ne _ _ _ _ h2]; exact hS⟩⟩

section un
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {SP0 P0 FM : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {J C SKB Nj H0 : BitVec 64} {M0 : Mem}

/-- Registry state inside the union: heap pointer at least `H0`, the registry with content at it, the journal
counter, every outside word as in `M0`. -/
def URS (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (H0 Nj : BitVec 64) (M0 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ H : BitVec 64, HeapIs G H ∧ H0.toNat ≤ H.toNat ∧ RegT n c T Out H M D B ko ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → M x = M0 x

/-- One union step `htab_set(dst, s.1, s.2)` on the registry table `kt ≠ ko`. -/
theorem unionSet_aqgd {LP : GA → Prop} {RR : ValueHOL 64 → Mem → GA → Prop} (kt : Fin n) (ne : kt ≠ ko) (p0 : P0.toNat ≤ H0.toNat) (hOut : Out w)
    (hl : ∀ L, LP L → L.lookup (ofString "dst") = some (.val (.word (T kt))) ∧
      ∃ a b d : BitVec 64, L.lookup (ofString "s") = some (.rStruct [.val (.word a),.val (.word b),.val (.word d)])) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun x => x ≠ ofString "s")
      (fun L M G => LP L ∧ URS n c T Out ko D B H0 Nj M0 M G) (fun L M G => LP L ∧ URS n c T Out ko D B H0 Nj M0 M G)
      RR
      (.call (some (none,none)) (ofString "htab_set")
        [.var .local (ofString "dst"),.rfield 1 (.var .local (ofString "s")),.rfield 2 (.var .local (ofString "s"))]) := by
  refine aqgd_conseq (P := fun L M G => ∃ q : (Fin n → TLay) × BitVec 64, LP L ∧ HeapIs G q.2 ∧
      H0.toNat ≤ q.2.toNat ∧ RegPure n c T Out q.2 q.1 ∧ RegMem n c T q.1 M ∧ TCont D B M (T ko) (q.1 ko) ∧
      (∀ x, (q.1 ko).arr x → x.toNat < q.2.toNat) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∀ x, Out x → M x = M0 x)
    (aqgd_ex (fun q => ?_)) (fun L M G ⟨lp,H,hH,hle,⟨l,pure,mem,tc,ab⟩,hn,fr⟩ =>
      ⟨(l,H),lp,hH,hle,pure,mem,tc,ab,hn,fr⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  rcases q with ⟨l,H⟩
  refine aqgd_callSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' G0' L M G => (∃ K V : BitVec 64, LK (irP0 (T kt) K V) L) ∧ M = M0' ∧ G = G0')
    (RRe := fun _ M0' G0' _ M' G' => G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∃ H' : BitVec 64, HeapIs G' H' ∧ SetPost (T kt) ((l kt).canon (T kt) H) M0' (l kt).C (l kt).SD (l kt).KS
        (l kt).VS (l kt).US (l kt).OS (l kt).OPS H M' H')
    _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,hH,hle,pure,mem,_,_,hn,_⟩
    have lay := (pure.1 kt).1
    have hwk : ¬ (l kt).canon (T kt) H w := pure.2.2 w hOut kt
    have p2 : P0.toNat ≤ H.toNat := by dsimp only at hle ⊢; omega
    refine aqgd_conseq (P := fun L M G => ∃ K V : BitVec 64, LK (irP0 (T kt) K V) L ∧ M = M0' ∧ G = G0')
      (aqgd_exE (fun K => aqgd_exE (fun V => aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
        originalRuntimeCode_hashSet_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
        (aqmh_rebound (set_aqmh (P0 := H) (T kt) K V _ (l kt).KL (l kt).SD (l kt).C (l kt).N (l kt).KS
          (l kt).VS (l kt).US (l kt).OS (l kt).OPS (l kt).b lay M0' hwk H (le_refl _)) p2)))
        (keepsSkBuf_of_installed originalRuntimeCode_hashSet_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_)))
      (fun L M G ⟨⟨K,V,hk⟩,hM,hG⟩ => ⟨K,V,hk,hM,hG⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
    · intro L M G ⟨hk,hM,hG⟩
      subst hM hG
      exact ⟨hn,H,hH,le_refl _,hk,(mem kt).2,rfl,rfl⟩
    · intro v M' G' ⟨hn',H',hH',post⟩
      exact ⟨hn',H',hH',post⟩
  · intro F s values callee rs _ G hG ⟨lp,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨hd,a,b,d,hs⟩ := hl _ lp
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hd,hs] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_hashSet_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨⟨b,d,fun p hp => ?_⟩,rfl,rfl⟩
    simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨lp,hH,hle,pure,mem,tc,ab,hn,frO⟩ ⟨hn',H',hH',post⟩
    exact ⟨lp,H',hH',le_trans hle post.1,regT_set ne l pure mem tc ab post,hn',
      fun x ho => (post.2.1 x (pure.2.2 x ho kt)).trans (frO x ho)⟩

#print axioms unionSet_aqgd
theorem aqgd_whileU {A : GA → Prop} {Vn : MlS → Prop} {I : GA → Mem → GA → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
    (c : ExpHOL 64) {body : ProgHOL 64}
    (hb : AQGD D B A w Vn (fun L M G => I L M G ∧ True) I RR body) :
    AQGD D B A w Vn I I RR (.while c body) :=
  aqgd_conseq (aqgd_whileBreak (I := I) (C := fun _ _ _ => True) (Qb := fun _ _ _ => False) _
      (fun _ _ _ _ _ _ _ _ => trivial) (aqgb_of_aqgd hb))
    (fun _ _ _ h => h) (fun _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h)

/-- Union-loop locals: `UL` and a word index `i`. -/
def ULi (Td : BitVec 64) (L : GA) : Prop :=
  UL Td L ∧ ∃ Iv : BitVec 64, L.lookup (ofString "i") = some (.val (.word Iv))

/-- The actual `htab_union_into(dst, src)` into the registry table `dst = T kt`, `kt ≠ ko`. -/
theorem htabUnionReg_aqgd (kt : Fin n) (ne : kt ≠ ko) (p0 : P0.toNat ≤ H0.toNat) (hOut : Out w) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun x => x ≠ ofString "s")
      (fun L M G => UL (T kt) L ∧ RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => URS n c T Out ko D B H0 Nj M0 M' G')
      (sourceFunctionBody Guest.guestFn_htab_union_into) := by
  rw [source_htabUnionInto_body]
  refine aqgd_conseq (P := fun L M G => UL (T kt) L ∧ URS n c T Out ko D B H0 Nj M0 M G) ?_
    (fun L M G ⟨ul,reg,hM,hH,hn⟩ => ⟨ul,H0,hH,le_refl _,reg,hn,fun x _ => by rw [hM]⟩) (fun _ _ _ h => h)
    (fun _ _ _ h => h)
  refine aqgd_decD (Qb := fun _ _ _ => True) (ofString "cap") .one _ (fun _ => rfl)
    (Pb := fun L M G => UL (T kt) L ∧ URS n c T Out ko D B H0 Nj M0 M G)
    (fun s v _ _ _ _ ⟨ul,rs⟩ _ _ _ => ⟨ul_upd ul _ v (by decide) (by decide),rs⟩) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_decD (Qb := fun _ _ _ => True) (ofString "i") .one _ (fun _ => rfl)
    (Pb := fun L M G => ULi (T kt) L ∧ URS n c T Out ko D B H0 Nj M0 M G)
    (fun s v _ _ _ _ ⟨ul,rs⟩ _ ev _ => by
      simp [EV,evalHOLExact] at ev; subst ev
      exact ⟨⟨ul_upd ul _ _ (by decide) (by decide),0#64,lookup_update_eq' _ _ _⟩,rs⟩) ?_
    (fun _ _ _ _ _ _ _ _ => trivial)
  refine aqgd_seq (aqgd_whileU _ ?_) (aqgd_return _ (fun _ _ _ _ _ ⟨_,rs⟩ _ _ => rs))
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => (ULi (T kt) L ∧ ∃ a b d : BitVec 64,
      L.lookup (ofString "s") = some (.rStruct [.val (.word a),.val (.word b),.val (.word d)])) ∧
      URS n c T Out ko D B H0 Nj M0 M G)
    (Qc := fun L M G => ULi (T kt) L ∧ URS n c T Out ko D B H0 Nj M0 M G)
    _ _ _ _ _ _ _ originalRuntimeCode_htabItem_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf htabItem_memoryFrame (by body_check Guest.guestFn_htab_item)
      (by body_check Guest.guestFn_htab_item) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => absurd rfl h) ?_ ?_
    (fun _ _ _ _ _ _ _ ⟨⟨ul,Iv,hi⟩,rs⟩ => ⟨⟨ul_res ul _ _ (by decide) (by decide),Iv,
      by rw [resVar_lookup_ne _ _ _ _ (by decide)]; exact hi⟩,rs⟩)
  · intro L M G v M' G' ⟨⟨⟨ul,Iv,hi⟩,rs⟩,_⟩ ⟨e1,e2⟩ ok
    subst e1 e2
    obtain ⟨a,b,d,rfl⟩ := triple_of_shape ok
    exact ⟨⟨⟨ul_upd ul _ _ (by decide) (by decide),Iv,by rw [lookup_update_ne' _ _ (by decide)]; exact hi⟩,
      a,b,d,lookup_update_eq' _ _ _⟩,rs⟩
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_conseq (unionSet_aqgd kt ne p0 hOut (fun L ⟨⟨ul,_⟩,hs⟩ => ⟨ul.1,hs⟩)) (fun _ _ _ h => h.1)
        (fun _ _ _ h => h) (fun _ _ _ h => h))
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)))
    (aqgd_assignLocal _ _ (fun s v _ _ ⟨⟨⟨ul,Iv,hi⟩,_⟩,rs⟩ _ ev => by
      simp [EV,evalHOLExact,evalListHOLExact,hi,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
      subst ev
      exact ⟨⟨ul_upd ul _ _ (by decide) (by decide),Iv + 1,lookup_update_eq' _ _ _⟩,rs⟩))

#print axioms htabUnionReg_aqgd
end un
end InitECandidate.Runtime
