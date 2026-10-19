import InitECandidate.Runtime.JDelHeapGD
import InitECandidate.Runtime.SkBufGlobalKeep
import InitECandidate.Runtime.HtabUnionInto
import InitECandidate.Runtime.VmFn_htab_item
import InitECandidate.Runtime.VmFn_sk_make
import InitECandidate.Runtime.OriginalJournalDeleteCode
/-!
Original `destroy_storage(addr)` in the fixed-domain triple `AQGD` over the journal arena with the key buffer
(`JWS`), on a table registry that carries the content invariant of the outer storage table (`RegT`: registry, `TCont`
of table `ko`, its arrays below the heap). The outer lookup (`htab_get`, read-only), the loop over the storage
table's order list (`htab_item` read-only, `sk_make` into `sk_buf`, `htab_set` on the destroyed-slot table `kd`), and
the journaled delete `jdel(outer, addr)` each re-establish `RegT` (`regT_frame`, `regT_set`, `regT_del`). Caller
premises (cells `ts + 32`/`ts + 24`, journal and key-buffer placement, watched word) are explicit.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Journal arena plus the key-scratch buffer pointer `sk_buf = SKB`. -/
def JWS (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB : BitVec 64) (g : GA) : Prop :=
  JW SP0 P0 FM G0 J C g ∧ g.lookup (ofString "sk_buf") = some (.val (.word SKB))

variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop} {SP0 P0 FM : BitVec 64} {G0 : GA}

/-- Lifting a journal-arena triple to `JWS` for a program keeping `sk_buf`. -/
theorem aqgd_jws {J C SKB : BitVec 64} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64}
    (h : AQGD D B (JW SP0 P0 FM G0 J C) w Vn P Q RR p) (hk : keepsG (ofString "sk_buf") goodJournalCap p = true) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w Vn P Q RR p :=
  aqgd_strengthen (X := fun g => g.lookup (ofString "sk_buf") = some (.val (.word SKB))) h
    (fun s code x => (evaluate_keeps_sk_buf p hk s code).trans x)

/-- Layout `l` with its count replaced. -/
def layN (l : TLay) (N' : BitVec 64) : TLay := ⟨l.KL,l.SD,l.C,N',l.KS,l.VS,l.US,l.OS,l.OPS,l.b⟩

theorem intabf_canon {T : BitVec 64} {l : TLay} {H x : BitVec 64}
    (h : InTabF T l.KS l.SD l.C l.US l.VS l.OS l.OPS x) : l.canon T H x := by
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem tcont_hdr {M : Mem} {T : BitVec 64} {l : TLay} (tc : TCont D B M T l) : l.hdr M T := by
  obtain ⟨F,s,sm,_,_,_,inv,_⟩ := tc
  subst sm
  exact ⟨inv.cell0,inv.cell8,inv.cell16,inv.cell24,inv.cell32,inv.cell40,inv.cell48,inv.cell56,inv.cell64⟩

/-- Registry with the content invariant of table `ko`, whose arrays lie below the heap pointer. -/
def RegT (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (H : BitVec 64) (M : Mem)
    (D : BitVec 64 → Prop) (B : Bool) (ko : Fin n) : Prop :=
  ∃ l : Fin n → TLay, RegPure n c T Out H l ∧ RegMem n c T l M ∧ TCont D B M (T ko) (l ko) ∧
    ∀ x, (l ko).arr x → x.toNat < H.toNat

theorem regT_mono {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H H' : BitVec 64} {M : Mem}
    {ko : Fin n} (h : RegT n c T Out H M D B ko) (le : H.toNat ≤ H'.toNat) : RegT n c T Out H' M D B ko := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h
  obtain ⟨tA,sep,o⟩ := regPure_tabs pure mem le
  exact ⟨l,⟨fun i => ⟨(tA i).2.1,(tA i).2.2.2⟩,sep,o⟩,mem,tc,fun x hx => by have := ab x hx; omega⟩

/-- A memory change confined to outside words that are no pointer cell keeps the registry with content. -/
theorem regT_frame {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M M' : Mem}
    {ko : Fin n} (h : RegT n c T Out H M D B ko) (S : BitVec 64 → Prop) (hS : ∀ x, S x → Out x ∧ ∀ i, x ≠ c i)
    (keep : ∀ x, ¬ S x → M' x = M x) : RegT n c T Out H M' D B ko := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h
  have fitT : ∀ i, (T i).toNat + 72 < 2 ^ 64 := fun i => by have := (pure.1 i).1.eEnd; omega
  refine ⟨l,pure,regMem_frame mem fitT (fun x ⟨i,hx⟩ => keep x (fun hs => ?_)),
    tc.frame (pure.1 ko).1.cnt.le (fun x hx => keep x (fun hs => pure.2.2 x (hS x hs).1 ko (intabf_canon hx))),ab⟩
  rcases hx with rfl | hx
  · exact (hS _ hs).2 i rfl
  · exact pure.2.2 x (hS x hs).1 i (Or.inl hx)

/-- A set on table `k` keeps all other tables' layouts. -/
theorem reg_set_keep {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H H' : BitVec 64} {M M' : Mem}
    (l : Fin n → TLay) (tA : ∀ i, TabAt (c i) (T i) (l i) H M) (sep : ∀ i j, i ≠ j → TabSep (T i) (l i) (c j) (T j) (l j) H)
    (o : ∀ x, Out x → ∀ i, ¬ (l i).canon (T i) H x) (k : Fin n)
    (post : SetPost (T k) ((l k).canon (T k) H) M (l k).C (l k).SD (l k).KS (l k).VS (l k).US (l k).OS (l k).OPS H M' H') :
    ∃ l' : Fin n → TLay, RegPure n c T Out H' l' ∧ RegMem n c T l' M' ∧ ∀ j, j ≠ k → l' j = l j := by
  obtain ⟨hle,ag,KL',SD',C',N',KS',VS',US',OS',OPS',b',hlay',hdr',inn⟩ := post
  let lk : TLay := ⟨KL',SD',C',N',KS',VS',US',OS',OPS',b'⟩
  have keepOut : ∀ x, ¬ (l k).canon (T k) H x → ¬ lk.canon (T k) H' x := by
    intro x hx hc
    rcases hc with h | h | h
    · exact hx (Or.inl h)
    · rcases inn x h with h' | ⟨lo,_⟩
      · exact hx (Or.inr (Or.inl h'))
      · exact hx (Or.inr (Or.inr lo))
    · exact hx (Or.inr (Or.inr (by omega)))
  classical
  let l' : Fin n → TLay := fun i => if i = k then lk else l i
  have hk : l' k = lk := by simp [l']
  have hj : ∀ j, j ≠ k → l' j = l j := fun j ne => by simp [l',ne]
  have other : ∀ j, j ≠ k → TabAt (c j) (T j) (l j) H' M' ∧ TabSep (T k) lk (c j) (T j) (l j) H' ∧
      TabSep (T j) (l j) (c k) (T k) lk H' := fun j ne =>
    set_sep' (lX' := lk) (tA j) (sep k j (Ne.symm ne)) (sep j k ne) hle ag inn
  have tA' : ∀ i, TabAt (c i) (T i) (l' i) H' M' := by
    intro i
    by_cases e : i = k
    · subst e; rw [hk]
      exact ⟨(ag _ (tA i).2.2.2).trans (tA i).1,hlay',hdr',keepOut _ (tA i).2.2.2⟩
    · rw [hj i e]; exact (other i e).1
  refine ⟨l',⟨fun i => ⟨(tA' i).2.1,(tA' i).2.2.2⟩,fun i j ne => ?_,fun x hx i => ?_⟩,
    fun i => ⟨(tA' i).1,(tA' i).2.2.1⟩,hj⟩
  · by_cases ei : i = k
    · subst ei; rw [hk,hj j (Ne.symm ne)]; exact (other j (Ne.symm ne)).2.1
    · by_cases ej : j = k
      · subst ej; rw [hk,hj i ei]; exact (other i ei).2.2
      · rw [hj i ei,hj j ej]; exact tabSep_mono (sep i j ne) hle
  · by_cases e : i = k
    · subst e; rw [hk]; exact keepOut x (o x hx i)
    · rw [hj i e]; exact fun cc => o x hx i (canon_mono cc hle)

/-- A set on table `kd ≠ ko` keeps the registry with the content of `ko`. -/
theorem regT_set {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H H' : BitVec 64} {M M' : Mem}
    {ko kd : Fin n} (ne : kd ≠ ko) (l : Fin n → TLay) (pure : RegPure n c T Out H l) (mem : RegMem n c T l M)
    (tc : TCont D B M (T ko) (l ko)) (ab : ∀ x, (l ko).arr x → x.toNat < H.toNat)
    (post : SetPost (T kd) ((l kd).canon (T kd) H) M (l kd).C (l kd).SD (l kd).KS (l kd).VS (l kd).US (l kd).OS
      (l kd).OPS H M' H') :
    RegT n c T Out H' M' D B ko := by
  have hle := post.1
  have ag := post.2.1
  obtain ⟨l',pure',mem',agree⟩ := reg_set_keep l (reg_of pure mem) pure.2.1 pure.2.2 kd post
  have e := agree ko (Ne.symm ne)
  refine ⟨l',pure',mem',?_,fun x hx => ?_⟩
  · rw [e]
    exact tc.frame (pure.1 ko).1.cnt.le (fun x hx => ag x (pure.2.1 kd ko ne x
      (by rcases hx with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h))))
  · rw [e] at hx; have := ab x hx; omega

/-- After a deletion in table `ko` (content invariant at the new count, memory below `H` kept outside the journal
and the table), the registry with content holds again. -/
theorem regT_del {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M M' : Mem}
    {ko : Fin n} {J C : BitVec 64} (l : Fin n → TLay) (pure : RegPure n c T Out H l) (mem : RegMem n c T l M)
    (ab : ∀ x, (l ko).arr x → x.toNat < H.toNat)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) (N' : BitVec 64) (hN : N'.toNat ≤ (l ko).N.toNat)
    (tc' : TCont D B M' (T ko) (layN (l ko) N'))
    (fr : ∀ x, x.toNat < H.toNat → ¬ InJ J C x →
      ¬ InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x → M' x = M x) :
    RegT n c T Out H M' D B ko := by
  classical
  let l' : Fin n → TLay := fun i => if i = ko then layN (l ko) N' else l i
  have hk : l' ko = layN (l ko) N' := by simp [l']
  have hj : ∀ j, j ≠ ko → l' j = l j := fun j ne => by simp [l',ne]
  have canonEq : ∀ i, (l' i).canon (T i) H = (l i).canon (T i) H := fun i => by
    by_cases e : i = ko
    · subst e; rw [hk]; rfl
    · rw [hj i e]
  have arrEq : ∀ i, (l' i).arr = (l i).arr := fun i => by
    by_cases e : i = ko
    · subst e; rw [hk]; rfl
    · rw [hj i e]
  have notIn : ∀ x, ¬ (l ko).canon (T ko) H x →
      ¬ InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x :=
    fun x hx hi => hx (intabf_canon hi)
  have cellKeep : ∀ i, M' (c i) = M (c i) := by
    intro i
    refine fr _ (regPure_below pure _ ⟨i,Or.inl rfl⟩) (fun hj => (jsep _ hj i).1 rfl) (notIn _ ?_)
    by_cases e : i = ko
    · subst e; exact (pure.1 i).2
    · exact pure.2.1 ko i (Ne.symm e) _ (Or.inl rfl)
  have fitT : ∀ i, (T i).toNat + 72 < 2 ^ 64 := fun i => by have := (pure.1 i).1.eEnd; omega
  refine ⟨l',⟨fun i => ⟨?_,?_⟩,fun i j ne => ?_,fun x hx i => ?_⟩,fun i => ⟨(cellKeep i).trans (mem i).1,?_⟩,
    by rw [hk]; exact tc',fun x hx => by rw [arrEq] at hx; exact ab x hx⟩
  · by_cases e : i = ko
    · subst e; rw [hk]
      have lay := (pure.1 i).1
      exact ⟨lay.pow,lay.fits,lay.sdAl,lay.ksAl,lay.usAl,by have := lay.cnt; simp only [layN]; omega,lay.hdr,
        lay.hdrP,lay.eEnd,lay.fresh,lay.keysR,lay.valsR,lay.usedR,lay.orderR,lay.oposR⟩
    · rw [hj i e]; exact (pure.1 i).1
  · rw [canonEq]; exact (pure.1 i).2
  · intro x hx; rw [canonEq]; rw [arrEq] at hx; exact pure.2.1 i j ne x hx
  · rw [canonEq]; exact pure.2.2 x hx i
  · by_cases e : i = ko
    · subst e; rw [hk]; exact tcont_hdr tc'
    · rw [hj i e]
      refine hdr_keep (mem i).2 (fitT i) (fun x lo hi => fr x ?_ (fun hJ => (jsep x hJ i).2 ⟨lo,hi⟩)
        (notIn x (pure.2.1 ko i (Ne.symm e) x (Or.inr (Or.inl ⟨lo,hi⟩)))))
      exact regPure_below pure x ⟨i,Or.inr ⟨lo,hi⟩⟩

#print axioms regT_del

/-- Bytes written by `sk_make`: the 20-byte address and 32-byte key windows of the key buffer. -/
def SkWin (SKB x : BitVec 64) : Prop := MWin SKB 20 x ∨ MWin (SKB + 20#64) 32 x

/-- The original `sk_make(addr, key)`: two memcpys into the key buffer `sk_buf = SKB`; returns `SKB`, keeps the
globals, and changes memory only inside `SkWin SKB`. -/
theorem skMake_aqgd {A : GA → Prop} {SKB : BitVec 64}
    (hA : ∀ g, A g → g.lookup (ofString "sk_buf") = some (.val (.word SKB))) (hw : ¬ SkWin SKB w)
    (M0 : Mem) (G1 : GA) :
    AQGD D B A w (fun _ => False)
      (fun L M G => (∃ a k : BitVec 64, L.lookup (ofString "addr") = some (.val (.word a)) ∧
        L.lookup (ofString "key") = some (.val (.word k))) ∧ M = M0 ∧ G = G1) (fun _ _ _ => True)
      (fun v M' G' => v = .val (.word SKB) ∧ G' = G1 ∧ ∀ x, ¬ SkWin SKB x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_sk_make) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_sk_make,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  refine aqgd_seq (Q := fun L M G => (∃ a k : BitVec 64, L.lookup (ofString "addr") = some (.val (.word a)) ∧
      L.lookup (ofString "key") = some (.val (.word k))) ∧ G = G1 ∧ ∀ x, ¬ MWin SKB 20 x → M x = M0 x)
    (aqgd_callSpec (Vn' := fun _ => False)
      (Pe := fun _ M0' G0' L M G => (∃ S : BitVec 64, L.lookup (ofString "dst") = some (.val (.word SKB)) ∧
        L.lookup (ofString "src") = some (.val (.word S)) ∧ L.lookup (ofString "n") = some (.val (.word 20#64))) ∧
        M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' _ M' G' => G' = G0' ∧ ∀ x, ¬ MWin SKB 20 x → M' x = M0' x)
      _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_) ?_
  · intro L0 M0' G0' _
    exact aqgd_of_window memcpy_body_globals_frame (by body_check Guest.guestFn_memcpy)
      (by body_check Guest.guestFn_memcpy) (MWin SKB 20)
      (fun s _ ⟨S,hd,hs,hn⟩ x hx => memcpy_body_window s SKB S 20#64 x hd hs hn (by decide) hx)
      (fun h => hw (Or.inl h)) M0' G0'
  · intro F s values callee rs aw G hG ⟨⟨a,k,ha,hk⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    have hs := hA _ aw
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hs,ha] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_memcpy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨a,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨hl,hM,hG⟩ ⟨eG,fr⟩
    subst hM hG eG
    exact ⟨hl,rfl,fr⟩
  refine aqgd_seq (Q := fun L M G => G = G1 ∧ ∀ x, ¬ SkWin SKB x → M x = M0 x)
    (aqgd_callSpec (Vn' := fun _ => False)
      (Pe := fun _ M0' G0' L M G => (∃ S : BitVec 64, L.lookup (ofString "dst") = some (.val (.word (SKB + 20#64))) ∧
        L.lookup (ofString "src") = some (.val (.word S)) ∧ L.lookup (ofString "n") = some (.val (.word 32#64))) ∧
        M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' _ M' G' => G' = G0' ∧ ∀ x, ¬ MWin (SKB + 20#64) 32 x → M' x = M0' x)
      _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_) (aqgd_return _ ?_)
  · intro L0 M0' G0' _
    exact aqgd_of_window memcpy_body_globals_frame (by body_check Guest.guestFn_memcpy)
      (by body_check Guest.guestFn_memcpy) (MWin (SKB + 20#64) 32)
      (fun s _ ⟨S,hd,hs,hn⟩ x hx => memcpy_body_window s (SKB + 20#64) S 32#64 x hd hs hn (by decide) hx)
      (fun h => hw (Or.inr h)) M0' G0'
  · intro F s values callee rs aw G hG ⟨⟨a,k,ha,hk⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    have hs := hA _ aw
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hs,hk,wordOpHOL,wordOp,valueIsWord,valueWord] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_memcpy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨k,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨_,hG,fr⟩ ⟨eG,fr'⟩
    subst hG eG
    exact ⟨rfl,fun x hx => (fr' x (fun h => hx (Or.inr h))).trans (fr x (fun h => hx (Or.inl h)))⟩
  · intro F s v H aw hG ⟨hg,fr⟩ _ ev
    unfold GIs at hG
    have hs := hA _ aw
    simp [EV,evalHOLExact,hs] at ev
    subst ev
    exact ⟨rfl,hg,fr⟩

#print axioms skMake_aqgd

theorem triple_of_shape {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one,.one,.one]) = true) :
    ∃ a b d : BitVec 64, v = .rStruct [.val (.word a),.val (.word b),.val (.word d)] := by
  rcases v with ⟨⟨y⟩⟩ | fs | ⟨n,fs⟩
  · simp [shapeOfHOLExact,shapeEqHOL] at h
  · rcases fs with _ | ⟨f1,_ | ⟨f2,_ | ⟨f3,_ | ⟨f4,rest⟩⟩⟩⟩
    · simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at h
    · simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at h
    · simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at h
    · rcases f1 with ⟨⟨a⟩⟩ | _ | _ <;> rcases f2 with ⟨⟨b⟩⟩ | _ | _ <;> rcases f3 with ⟨⟨d⟩⟩ | _ | _ <;>
        simp_all [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
    · simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at h
  · simp [shapeOfHOLExact,shapeEqHOL] at h

/-- Locals of `destroy_storage` kept through its loop. -/
def DSL (A To : BitVec 64) (L : GA) : Prop :=
  L.lookup (ofString "addr") = some (.val (.word A)) ∧ L.lookup (ofString "outer") = some (.val (.word To)) ∧
    (∃ a b : BitVec 64, L.lookup (ofString "m") = some (.rStruct [.val (.word a),.val (.word b)])) ∧
    (∃ x : BitVec 64, L.lookup (ofString "inner") = some (.val (.word x))) ∧
    (∃ x : BitVec 64, L.lookup (ofString "cap") = some (.val (.word x))) ∧
    (∃ x : BitVec 64, L.lookup (ofString "i") = some (.val (.word x)))

def dsNames : List MlS :=
  [ofString "addr",ofString "outer",ofString "m",ofString "inner",ofString "cap",ofString "i"]

theorem dsl_update {A To : BitVec 64} {L : GA} (h : DSL A To L) {x : MlS} (hx : x ∉ dsNames) (v : ValueHOL 64) :
    DSL A To (L.update (x,v)) := by
  have ne : ∀ y ∈ dsNames, (L.update (x,v)).lookup y = L.lookup y := fun y hy => by
    have : y ≠ x := fun e => hx (e ▸ hy)
    simp [HolFiniteMapExact.lookup_update,FUPDATE,this,Ne.symm this]
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := h
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> rw [ne _ (by simp [dsNames])] <;> assumption

theorem dsl_res {A To : BitVec 64} {L : GA} (h : DSL A To L) {x : MlS} (hx : x ∉ dsNames) (o : Option (ValueHOL 64)) :
    DSL A To (L.resVarEq (x,o)) := by
  have ne : ∀ y ∈ dsNames, (L.resVarEq (x,o)).lookup y = L.lookup y := fun y hy =>
    resVar_lookup_ne L x y o (fun e => hx (e ▸ hy))
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := h
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> rw [ne _ (by simp [dsNames])] <;> assumption

/-- Memory/globals part of the `destroy_storage` loop state: heap above the entry heap, registry with content of
`ko`, counter unchanged, outside words outside the key buffer kept. -/
def DSM (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (SKB H0 Nj : BitVec 64) (M0 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ H : BitVec 64, HeapIs G H ∧ H0.toNat ≤ H.toNat ∧ RegT n c T Out H M D B ko ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ SkWin SKB x → M x = M0 x

/-- Exit of `destroy_storage`. -/
def DSPost (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (J C SKB H0 Nj : BitVec 64) (M0 : Mem) (M' : Mem) (G' : GA) : Prop :=
  ∃ H' : BitVec 64, HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ RegT n c T Out H' M' D B ko ∧
    (G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∨
      (Nj.toNat < C.toNat ∧ G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))))) ∧
    ∀ x, Out x → ¬ InJ J C x → ¬ SkWin SKB x → M' x = M0 x

section ds
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kd : Fin n}
  {Ts SKB J C Nj H0 : BitVec 64} {M0 : Mem}

set_option maxHeartbeats 16000000 in
/-- The original `destroy_storage(addr)` over a registry with the content of the outer storage table `ko` (cell
`ts + 32`) and the destroyed-slot table `kd` (cell `ts + 24`): the watched word (an outside word, outside the journal,
below `P0`, outside the key buffer) is kept in every outcome, and every return satisfies `DSPost`. -/
theorem destroyStorage_aqgd (ne : kd ≠ ko) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hco : c ko = Ts + 32#64) (hcd : c kd = Ts + 24#64)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w) (hwS : ¬ SkWin SKB w) (hJO : ∀ x, InJ J C x → Out x)
    (hSO : ∀ x, SkWin SKB x → Out x ∧ ∀ i, x ≠ c i)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) :
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun x => x ≠ ofString "m" ∧ x ≠ ofString "s")
      (fun L M G => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
        RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True) (fun _ M' G' => DSPost n c T Out ko D B J C SKB H0 Nj M0 M' G')
      (sourceFunctionBody Guest.guestFn_destroy_storage) := by
  -- the pointer cells `ts + 32`, `ts + 24` through the static global `ts`
  have cellEv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (k : Fin n) (off : BitVec 64), c k = Ts + off →
      JWS SP0 P0 FM G0 J C SKB s.globals → s.memory (c k) = .word (T k) → ∀ v,
      EV s (.load .one (.op .add [.var .global (ofString "ts"),.const off])) = some v → v = .val (.word (T k)) := by
    intro F s k off hc aw hm v ev
    obtain ⟨eg,_⟩ := aw.1.1.2.2.2 (ofString "ts") (by decide)
    rw [hc] at hm
    simp [EV,evalHOLExact,evalListHOLExact,eg,hTs,wordOpHOL,wordOp,valueIsWord,valueWord,memLoadHOLExact,hm] at ev
    exact ev.2.symm
  refine aqgd_conseq (P := fun L M G => ∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A)) ∧
      RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (aqgd_ex (fun A => ?_)) (fun L M G ⟨⟨A,hA⟩,r⟩ => ⟨A,hA,r⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_destroy_storage,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  -- outer = lds (ts + 32)
  refine aqgd_dec (Pb := fun L M G => L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "outer") = some (.val (.word (T ko))) ∧
      RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Qb := fun _ _ _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v G aw hG ⟨ha,reg,hM,hH,hn⟩ _ ev _
    obtain ⟨l,_,mem,_⟩ := reg
    rw [cellEv s ko 32#64 hco aw (mem ko).1 v ev]
    exact ⟨by simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using ha,
      by simp [HolFiniteMapExact.lookup_update,FUPDATE],⟨l,‹_›,mem,‹_›⟩,hM,hH,hn⟩
  -- m = htab_get(outer, addr): read-only
  refine aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => (L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "outer") = some (.val (.word (T ko))) ∧
      ∃ a b : BitVec 64, L.lookup (ofString "m") = some (.rStruct [.val (.word a),.val (.word b)])) ∧
      RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp)
    (fun _ M0' G0' _ => aqgd_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => absurd rfl h.1) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro L M G v M' G' ⟨ha,ho,rest⟩ ⟨e1,e2⟩ ok
    subst e1 e2
    obtain ⟨a,b,rfl⟩ := pair_of_shape ok
    refine ⟨⟨?_,?_,a,b,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rest⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  -- absent storage: return 0 with nothing changed
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
      (aqgd_return _ (fun s v H _ hG ⟨⟨_,reg,hM,hH,hn⟩,_⟩ _ _ =>
        ⟨H0,hH,le_refl _,reg,Or.inl hn,fun x _ _ _ => by rw [hM]⟩))
      (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h))) ?_
  -- inner = m.1; cap = lds (inner + 24); i = 0
  refine aqgd_dec (Pb := fun L M G => ((L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "outer") = some (.val (.word (T ko))) ∧
      ∃ a b : BitVec 64, L.lookup (ofString "m") = some (.rStruct [.val (.word a),.val (.word b)])) ∧
      ∃ x : BitVec 64, L.lookup (ofString "inner") = some (.val (.word x))) ∧
      RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Qb := fun _ _ _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v G _ _ ⟨⟨ha,ho,a,b,hm⟩,rest⟩ _ ev _
    simp [EV,evalHOLExact,hm] at ev
    subst ev
    refine ⟨⟨⟨?_,?_,a,b,?_⟩,b,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rest⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  refine aqgd_dec (Pb := fun L M G => (((L.lookup (ofString "addr") = some (.val (.word A)) ∧
      L.lookup (ofString "outer") = some (.val (.word (T ko))) ∧
      ∃ a b : BitVec 64, L.lookup (ofString "m") = some (.rStruct [.val (.word a),.val (.word b)])) ∧
      ∃ x : BitVec 64, L.lookup (ofString "inner") = some (.val (.word x))) ∧
      ∃ x : BitVec 64, L.lookup (ofString "cap") = some (.val (.word x))) ∧
      RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Qb := fun _ _ _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v G _ _ ⟨⟨⟨ha,ho,a,b,hm⟩,x,hx⟩,rest⟩ _ ev _
    obtain ⟨y,rfl⟩ := ev_load_one_word s _ v ev
    refine ⟨⟨⟨⟨?_,?_,a,b,?_⟩,x,?_⟩,y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rest⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  refine aqgd_dec (Pb := fun L M G => DSL A (T ko) L ∧ DSM n c T Out ko D B SKB H0 Nj M0 M G)
    (Qb := fun _ _ _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v G _ _ ⟨⟨⟨⟨ha,ho,a,b,hm⟩,x,hx⟩,y,hy⟩,reg,hM,hH,hn⟩ _ ev _
    simp [EV,evalHOLExact] at ev
    subst ev
    refine ⟨⟨?_,?_,⟨a,b,?_⟩,⟨x,?_⟩,⟨y,?_⟩,⟨0,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩⟩,
      H0,hH,le_refl _,reg,hn,fun x _ _ => by rw [hM]⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  -- the loop over the storage table's order list, then the journaled delete of the storage entry
  refine aqgd_seq (Q := fun L M G => DSL A (T ko) L ∧ DSM n c T Out ko D B SKB H0 Nj M0 M G)
    (aqgd_conseq (aqgd_whileBreak (I := fun L M G => DSL A (T ko) L ∧ DSM n c T Out ko D B SKB H0 Nj M0 M G)
      (C := fun _ _ _ => True) (Qb := fun L M G => DSL A (T ko) L ∧ DSM n c T Out ko D B SKB H0 Nj M0 M G) _
      (fun _ _ _ _ _ _ _ _ => trivial) (aqgb_of_aqgd ?_)) (fun _ _ _ h => h) (fun _ _ _ h => h.elim id id)
      (fun _ _ _ h => h)) ?_
  · -- s = htab_item(inner, i): read-only
    refine aqgd_decCallSpec (Vn' := fun _ => False)
      (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
      (Pc := fun L M G => (DSL A (T ko) L ∧ ∃ a b d : BitVec 64,
        L.lookup (ofString "s") = some (.rStruct [.val (.word a),.val (.word b),.val (.word d)])) ∧
        DSM n c T Out ko D B SKB H0 Nj M0 M G)
      (Qc := fun L M G => DSL A (T ko) L ∧ DSM n c T Out ko D B SKB H0 Nj M0 M G)
      _ _ _ _ _ _ _ vmLookup_htab_item (by simp)
      (fun _ M0' G0' _ => aqgd_of_mf htabItem_memoryFrame (by body_check Guest.guestFn_htab_item)
        (by body_check Guest.guestFn_htab_item) M0' G0')
      (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => absurd rfl h.2) ?_ ?_
      (fun _ _ _ _ _ _ _ ⟨hl,hm⟩ => ⟨dsl_res hl (by decide) _,hm⟩)
    · intro L M G v M' G' ⟨⟨hl,hm⟩,_⟩ ⟨e1,e2⟩ ok
      subst e1 e2
      obtain ⟨a,b,d,rfl⟩ := triple_of_shape ok
      exact ⟨⟨dsl_update hl (by decide) _,a,b,d,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,hm⟩
    refine aqgd_seq (Q := fun L M G => (DSL A (T ko) L ∧ ∃ a b d : BitVec 64,
        L.lookup (ofString "s") = some (.rStruct [.val (.word a),.val (.word b),.val (.word d)])) ∧
        DSM n c T Out ko D B SKB H0 Nj M0 M G)
      (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
        (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
        (aqgd_conseq aqgd_skip (fun _ _ _ h => h) (fun _ _ _ h => h.1) (fun _ _ _ h => h)))
      (aqgd_assignLocal _ _ ?_)
    rotate_left
    · intro F s v _ _ ⟨⟨⟨h1,h2,h3,h4,h5,x,hx⟩,_⟩,hm⟩ _ ev
      simp [EV,evalHOLExact,evalListHOLExact,hx,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
      subst ev
      refine ⟨⟨?_,?_,?_,?_,?_,x + 1#64,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,hm⟩
      · simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using h1
      · simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using h2
      · simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using h3
      · simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using h4
      · simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using h5
    -- k = sk_make(addr, s.1); htab_set(lds (ts + 24), k, 1)
    refine aqgd_decCallSpec (Vn' := fun _ => False)
      (Pe := fun _ M0' G0' L M G => (∃ a k : BitVec 64, L.lookup (ofString "addr") = some (.val (.word a)) ∧
        L.lookup (ofString "key") = some (.val (.word k))) ∧ M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' v M' G' => v = .val (.word SKB) ∧ G' = G0' ∧ ∀ x, ¬ SkWin SKB x → M' x = M0' x)
      (Pc := fun L M G => ((DSL A (T ko) L ∧ ∃ a b d : BitVec 64,
        L.lookup (ofString "s") = some (.rStruct [.val (.word a),.val (.word b),.val (.word d)])) ∧
        L.lookup (ofString "k") = some (.val (.word SKB))) ∧ DSM n c T Out ko D B SKB H0 Nj M0 M G)
      (Qc := fun L M G => (DSL A (T ko) L ∧ ∃ a b d : BitVec 64,
        L.lookup (ofString "s") = some (.rStruct [.val (.word a),.val (.word b),.val (.word d)])) ∧
        DSM n c T Out ko D B SKB H0 Nj M0 M G)
      _ _ _ _ _ _ _ vmLookup_sk_make (by simp) (fun _ M0' G0' _ => skMake_aqgd (fun g h => h.2) hwS M0' G0')
      ?_ (fun _ => rfl) ?_ ?_ ?_
    · intro F s values callee rs _ G hG ⟨⟨⟨⟨ha,_⟩,a,b,d,hs⟩,_⟩,_⟩ _ args lookup
      unfold GIs at hG; subst hG
      rw [evalListHOLFinite_eq_toExact] at args
      simp [evalListHOLExact,evalHOLExact,ha,hs] at args
      subst args
      rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) vmLookup_sk_make] at lookup
      simp only [Option.some.injEq,Prod.mk.injEq] at lookup
      obtain ⟨_,rfl,_⟩ := lookup
      exact ⟨⟨A,b,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
        by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
    · intro L M G v M' G' ⟨⟨⟨hl,a,b,d,hs⟩,hm⟩,_⟩ ⟨ev,eG,fr⟩ _
      subst ev eG
      obtain ⟨H,hH,hle,reg,hn,frO⟩ := hm
      refine ⟨⟨⟨dsl_update hl (by decide) _,a,b,d,?_⟩,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,
        H,hH,hle,regT_frame reg (SkWin SKB) hSO (fun x hx => fr x hx),hn,
        fun x ho hsk => (fr x hsk).trans (frO x ho hsk)⟩
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using hs
    · refine aqgd_conseq (P := fun L M G => ∃ q : (Fin n → TLay) × BitVec 64, ((DSL A (T ko) L ∧ ∃ a b d : BitVec 64,
          L.lookup (ofString "s") = some (.rStruct [.val (.word a),.val (.word b),.val (.word d)])) ∧
          L.lookup (ofString "k") = some (.val (.word SKB))) ∧ HeapIs G q.2 ∧ H0.toNat ≤ q.2.toNat ∧
          RegPure n c T Out q.2 q.1 ∧ RegMem n c T q.1 M ∧ TCont D B M (T ko) (q.1 ko) ∧
          (∀ x, (q.1 ko).arr x → x.toNat < q.2.toNat) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
          ∀ x, Out x → ¬ SkWin SKB x → M x = M0 x)
        (aqgd_ex (fun q => ?_)) (fun L M G ⟨hl,H,hH,hle,⟨l,pure,mem,tc,ab⟩,hn,fr⟩ =>
          ⟨(l,H),hl,hH,hle,pure,mem,tc,ab,hn,fr⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
      rcases q with ⟨l,H⟩
      refine aqgd_callSpec (Vn' := fun _ => True)
        (Pe := fun _ M0' G0' L M G => LK (irP0 (T kd) SKB 1#64) L ∧ M = M0' ∧ G = G0')
        (RRe := fun _ M0' G0' _ M' G' => G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
          ∃ H' : BitVec 64, HeapIs G' H' ∧ SetPost (T kd) ((l kd).canon (T kd) H) M0' (l kd).C (l kd).SD (l kd).KS
            (l kd).VS (l kd).US (l kd).OS (l kd).OPS H M' H')
        _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ ?_
      · intro L0 M0' G0' ⟨_,hH,hle,pure,mem,_,_,hn,_⟩
        have lay := (pure.1 kd).1
        have hwk : ¬ (l kd).canon (T kd) H w := pure.2.2 w hOut kd
        have p2 : P0.toNat ≤ H.toNat := by dsimp only at hle ⊢; omega
        refine aqgd_conseq (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
          originalRuntimeCode_hashSet_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
          (aqmh_rebound (set_aqmh (P0 := H) (T kd) SKB 1#64 _ (l kd).KL (l kd).SD (l kd).C (l kd).N (l kd).KS
            (l kd).VS (l kd).US (l kd).OS (l kd).OPS (l kd).b lay M0' hwk H (le_refl _)) p2)))
          (keepsSkBuf_of_installed originalRuntimeCode_hashSet_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
        · intro L M G ⟨hl,hM,hG⟩
          subst hM hG
          exact ⟨hn,H,hH,le_refl _,hl,(mem kd).2,rfl,rfl⟩
        · intro v M' G' ⟨hn',H',hH',post⟩
          exact ⟨hn',H',hH',post⟩
      · intro F s values callee rs aw G hG ⟨⟨_,hk⟩,_,_,_,mem,_⟩ _ args lookup
        unfold GIs at hG; subst hG
        rw [evalListHOLFinite_eq_toExact] at args
        cases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
            (.load .one (.op .add [.var .global (ofString "ts"),.const 24#64])) with
        | none => simp [evalListHOLExact,h1] at args
        | some x1 =>
          have e1 := cellEv s kd 24#64 hcd aw (mem kd).1 x1 h1
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
          fun x ho hsk => (post.2.1 x (pure.2.2 x ho kd)).trans (frO x ho hsk)⟩
    · intro L M G L' M' G' _ ⟨⟨hl,a,b,d,hs⟩,hm⟩
      exact ⟨⟨dsl_res hl (by decide) _,a,b,d,by rw [resVar_lookup_ne _ _ _ _ (by decide)]; exact hs⟩,hm⟩
  refine aqgd_seq (Q := fun _ M' G' => DSPost n c T Out ko D B J C SKB H0 Nj M0 M' G') ?_
    (aqgd_return _ (fun _ _ _ _ _ h _ _ => h))
  refine aqgd_conseq (P := fun L M G => ∃ q : (Fin n → TLay) × BitVec 64, DSL A (T ko) L ∧ HeapIs G q.2 ∧
      H0.toNat ≤ q.2.toNat ∧ RegPure n c T Out q.2 q.1 ∧ RegMem n c T q.1 M ∧ TCont D B M (T ko) (q.1 ko) ∧
      (∀ x, (q.1 ko).arr x → x.toNat < q.2.toNat) ∧ G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧
      ∀ x, Out x → ¬ SkWin SKB x → M x = M0 x)
    (aqgd_ex (fun q => ?_)) (fun L M G ⟨hl,H,hH,hle,⟨l,pure,mem,tc,ab⟩,hn,fr⟩ =>
      ⟨(l,H),hl,hH,hle,pure,mem,tc,ab,hn,fr⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  rcases q with ⟨l,H⟩
  dsimp only
  refine aqgd_callSpec (Vn' := fun x => x ≠ ofString "old")
    (Pe := fun _ M0' _ L M G => JLd (T ko) A L ∧ M = M0' ∧ HeapIs G H ∧
      G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (RRe := fun _ M0' _ _ M' G' => JDPost D B (T ko) (l ko) J C Nj H M0' M' G')
    _ _ _ _ _ originalRuntimeCode_journalDelete_lookup (by simp) ?_ ?_ ?_
  · intro L0 M0' G0' ⟨_,_,hle,pure,_,tc,ab,_,_⟩
    have lay := (pure.1 ko).1
    have below : ∀ x, InTabF (T ko) (l ko).KS (l ko).SD (l ko).C (l ko).US (l ko).VS (l ko).OS (l ko).OPS x →
        x.toNat < H.toNat := by
      intro x hx
      rcases hx with hh | ha
      · have := lay.hdrP; omega
      · exact ab x ha
    exact aqgd_jws (jdel_aqgd (T ko) A J C Nj H (l ko) M0' tc lay.cnt (by omega) jfit hwJ hwP
      (fun h => pure.2.2 w hOut ko (intabf_canon h)) below
      (fun x hj h => pure.2.2 x (hJO x hj) ko (intabf_canon h)))
      (keepsSkBuf_of_installed originalRuntimeCode_journalDelete_lookup (by decide))
  · intro F s values callee rs _ G hG ⟨⟨ha,ho,_⟩,hH,_,_,_,_,_,hn,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,ha,ho] at args
    subst args
    rw [pan_two_word_lookup _ _ _ _ _ _ _ (by decide) originalRuntimeCode_journalDelete_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,hH,hn⟩
  · intro L M G v M' G' ⟨_,_,hle,pure,mem,_,ab,_,frO⟩ ⟨H',hH',hle',hjn,⟨N',hN',tc'⟩,fr⟩
    have reg := regT_del l pure mem ab jsep N' (by rcases hN' with rfl | h <;> omega) tc' fr
    refine ⟨H',hH',le_trans hle hle',regT_mono reg hle',hjn,fun x ho hj hsk => ?_⟩
    have ltH : x.toNat < H.toNat := by
      by_contra h; exact pure.2.2 x ho ko (Or.inr (Or.inr (by omega)))
    exact (fr x ltH hj (fun h => pure.2.2 x ho ko (intabf_canon h))).trans (frO x ho hsk)

#print axioms destroyStorage_aqgd
end ds

#print axioms regT_frame
#print axioms regT_set
end InitECandidate.Runtime
