import InitECandidate.Runtime.PreStateHeap
import InitECandidate.Runtime.OriginalAccountCode
import InitECandidate.Runtime.PreStateAccountHeap
/-!
Registry of any number of hash tables (`Reg`): each valid against its canonical footprint with cell and header in
memory, pairwise separated, given words outside all footprints.  `reg_set` re-establishes it after a set on one
table; `preStateReg_aqmh`, `accountOptReg_aqmh`, `accountReg_aqmh` are the heap-aware original
`get_pre_state_account_optional`, `get_account_optional` and `get_account` over a registry containing the `ts + 8`
and `bs + 72` tables, preserving every registry table.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A registry of `n` tables at heap pointer `H`: table `i` has pointer cell `c i` and header `T i`; each is valid
against its canonical footprint with header in memory, all are pairwise separated (cell, header and arrays of each
outside every other footprint), and the words `Out` lie outside every footprint. -/
def Reg (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (H : BitVec 64) (M : Mem) : Prop :=
  ∃ l : Fin n → TLay, (∀ i, TabAt (c i) (T i) (l i) H M) ∧
    (∀ i j, i ≠ j → TabSep (T i) (l i) (c j) (T j) (l j) H) ∧ (∀ x, Out x → ∀ i, ¬ (l i).canon (T i) H x)

/-- A set on table `X` with explicit new layout `lX'` keeps any separated table `Y` and both separations. -/
theorem set_sep' {cX TX cY TY : BitVec 64} {lX lX' lY : TLay} {H H' : BitVec 64} {M M' : Mem}
    (tY : TabAt cY TY lY H M) (sXY : TabSep TX lX cY TY lY H) (sYX : TabSep TY lY cX TX lX H)
    (hle : H.toNat ≤ H'.toNat) (ag : ∀ x, ¬ lX.canon TX H x → M' x = M x)
    (inn : LayIn (fun x => lX.arr x ∨ (H.toNat ≤ x.toNat ∧ x.toNat < H'.toNat)) lX'.C lX'.SD lX'.KS lX'.VS lX'.US
      lX'.OS lX'.OPS) :
    TabAt cY TY lY H' M' ∧ TabSep TX lX' cY TY lY H' ∧ TabSep TY lY cX TX lX' H' := by
  have keepOut : ∀ x, ¬ lX.canon TX H x → ¬ lX'.canon TX H' x := by
    intro x hx hc
    rcases hc with h | h | h
    · exact hx (Or.inl h)
    · rcases inn x h with h' | ⟨lo,_⟩
      · exact hx (Or.inr (Or.inl h'))
      · exact hx (Or.inr (Or.inr lo))
    · exact hx (Or.inr (Or.inr (by omega)))
  have fitY : TY.toNat + 72 < 2 ^ 64 := by have := tY.2.1.eEnd; omega
  refine ⟨⟨(ag _ (sXY _ (Or.inl rfl))).trans tY.1,hlay_canon tY.2.1 hle,
      hdr_keep tY.2.2.1 fitY (fun x lo hi => ag x (sXY x (Or.inr (Or.inl ⟨lo,hi⟩)))),
      fun hc => tY.2.2.2 (canon_mono hc hle)⟩,fun x hx => keepOut x (sXY x hx),?_⟩
  intro x hx hc
  rcases hx with hx | hx | hx
  · exact sYX x (Or.inl hx) (canon_mono hc hle)
  · exact sYX x (Or.inr (Or.inl hx)) (canon_mono hc hle)
  · rcases inn x hx with h | ⟨lo,hi⟩
    · exact sYX x (Or.inr (Or.inr h)) (canon_mono hc hle)
    · rcases hc with h | h | h
      · have := tY.2.1.hdrP; obtain ⟨_,_⟩ := h; omega
      · exact sXY x (Or.inr (Or.inr h)) (Or.inr (Or.inr lo))
      · omega

theorem reg_mono {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H H' : BitVec 64} {M : Mem}
    (h : Reg n c T Out H M) (le : H.toNat ≤ H'.toNat) : Reg n c T Out H' M := by
  obtain ⟨l,tA,sep,o⟩ := h
  exact ⟨l,fun i => tabAt_mono (tA i) le,fun i j ne => tabSep_mono (sep i j ne) le,
    fun x hx i hc => o x hx i (canon_mono hc le)⟩

/-- The registry only depends on the tables' cell and header words. -/
theorem reg_frame {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M M' : Mem}
    (h : Reg n c T Out H M) (keep : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → M' x = M x) : Reg n c T Out H M' := by
  obtain ⟨l,tA,sep,o⟩ := h
  refine ⟨l,fun i => ?_,sep,o⟩
  have fit : (T i).toNat + 72 < 2 ^ 64 := by have := (tA i).2.1.eEnd; omega
  exact ⟨(keep _ ⟨i,Or.inl rfl⟩).trans (tA i).1,(tA i).2.1,
    hdr_keep (tA i).2.2.1 fit (fun x lo hi => keep x ⟨i,Or.inr ⟨lo,hi⟩⟩),(tA i).2.2.2⟩

/-- Cells and headers of registry tables lie below the heap pointer. -/
theorem reg_below {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    (h : Reg n c T Out H M) (x : BitVec 64) (hx : ∃ i, x = c i ∨ HdrR (T i) x) : x.toNat < H.toNat := by
  obtain ⟨l,tA,_,_⟩ := h
  obtain ⟨i,rfl | ⟨_,hi⟩⟩ := hx
  · by_contra cc; exact (tA i).2.2.2 (Or.inr (Or.inr (by omega)))
  · have := (tA i).2.1.hdrP; omega

/-- A set on registry table `k` (started at heap pointer `H` against footprint `(l k).canon`) re-establishes the
registry at the exit heap pointer. -/
theorem reg_set {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H H' : BitVec 64} {M M' : Mem}
    (l : Fin n → TLay) (tA : ∀ i, TabAt (c i) (T i) (l i) H M) (sep : ∀ i j, i ≠ j → TabSep (T i) (l i) (c j) (T j) (l j) H)
    (o : ∀ x, Out x → ∀ i, ¬ (l i).canon (T i) H x) (k : Fin n)
    (post : SetPost (T k) ((l k).canon (T k) H) M (l k).C (l k).SD (l k).KS (l k).VS (l k).US (l k).OS (l k).OPS H M' H') :
    Reg n c T Out H' M' := by
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
  refine ⟨l',fun i => ?_,fun i j ne => ?_,fun x hx i => ?_⟩
  · by_cases e : i = k
    · subst e; rw [hk]
      exact ⟨(ag _ (tA i).2.2.2).trans (tA i).1,hlay',hdr',keepOut _ (tA i).2.2.2⟩
    · rw [hj i e]; exact (other i e).1
  · by_cases ei : i = k
    · subst ei; rw [hk,hj j (Ne.symm ne)]; exact (other j (Ne.symm ne)).2.1
    · by_cases ej : j = k
      · subst ej; rw [hk,hj i ei]; exact (other i ei).2.2
      · rw [hj i ei,hj j ej]; exact tabSep_mono (sep i j ne) hle
  · by_cases e : i = k
    · subst e; rw [hk]; exact keepOut x (o x hx i)
    · rw [hj i e]; exact fun cc => o x hx i (canon_mono cc hle)

#print axioms set_sep'

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)}

/-- Layout facts of a registry (independent of memory). -/
def RegPure (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (H : BitVec 64) (l : Fin n → TLay) : Prop :=
  (∀ i, (l i).ok (T i) H ∧ ¬ (l i).canon (T i) H (c i)) ∧
    (∀ i j, i ≠ j → TabSep (T i) (l i) (c j) (T j) (l j) H) ∧ (∀ x, Out x → ∀ i, ¬ (l i).canon (T i) H x)

/-- Memory facts of a registry: pointer cells and headers. -/
def RegMem (n : Nat) (c T : Fin n → BitVec 64) (l : Fin n → TLay) (M : Mem) : Prop :=
  ∀ i, M (c i) = .word (T i) ∧ (l i).hdr M (T i)

theorem reg_of {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    {l : Fin n → TLay} (hp : RegPure n c T Out H l) (hm : RegMem n c T l M) :
    ∀ i, TabAt (c i) (T i) (l i) H M := fun i => ⟨(hm i).1,(hp.1 i).1,(hm i).2,(hp.1 i).2⟩

set_option maxHeartbeats 8000000 in
/-- Heap-aware `get_pre_state_account_optional` over a registry of tables containing the transaction read table
(index `kA`, cell `ts + 8`) and the block pre-state read table (index `kB`, cell `bs + 72`): from the registry at
entry heap `H0`, every return re-establishes the whole registry at the exit heap pointer, with the watched word
(one of the outside words `Out`) kept in every outcome.  All registry cells and headers must avoid the scratch arena
and the Keccak/nibble buffers. -/
theorem preStateReg_aqmh (n : Nat) (c T : Fin n → BitVec 64) (kA kB : Fin n) (Ts Bs : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (Out : BitVec 64 → Prop) (hOut : Out w)
    (H0 : BitVec 64) (p0 : P0.toNat ≤ H0.toNat) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (ws : WsSafe SP0 FM K Pd NB w) (hp : w.toNat < P0.toNat) :
    AQMH SP0 P0 FM G0 w (fun x => x ≠ ofString "w")
      (fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0 ∧
        Reg n c T Out H0 M)
      (fun _ _ _ => True) (fun _ M' H' => Reg n c T Out H' M')
      (sourceFunctionBody Guest.guestFn_get_pre_state_account_optional) := by
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
  refine aqmh_conseq (P := fun L M H => ∃ l : Fin n → TLay, RegPure n c T Out H0 l ∧
    ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0 ∧ RegMem n c T l M))
    (aqmh_ex (fun l => aqmh_pure_pre (fun pf => ?_)))
    (fun L M H ⟨ha,he,l,tA,sep,o⟩ => ⟨l,⟨fun i => ⟨(tA i).2.1,(tA i).2.2.2⟩,sep,o⟩,ha,he,
      fun i => ⟨(tA i).1,(tA i).2.2.1⟩⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  -- record the transaction read (htab_set on the table at ts + 8)
  refine aqmh_seq (Q := fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      H0.toNat ≤ H.toNat ∧ Reg n c T Out H M)
    (aqmh_setCall (ofString "ts") (by decide) Ts 8 hTs _ _ (T kA) (l kA).KL (l kA).SD (l kA).C (l kA).N (l kA).KS
      (l kA).VS (l kA).US (l kA).OS (l kA).OPS (l kA).b H0 (pf.1 kA).1 (pf.2.2 w hOut kA) p0
      (fun L M H h => ⟨h.2.1,hcA ▸ (h.2.2 kA).1,(h.2.2 kA).2⟩) ?_ ?_) ?_
  · intro F s x H ⟨⟨A,hA⟩,_⟩ _ hx
    rcases hx with hx | hx
    · simp [EV,evalHOLExact,hA] at hx; exact ⟨A,hx.symm⟩
    · simp [EV,evalHOLExact] at hx; exact ⟨1,hx.symm⟩
  · intro L M H M' H' ⟨ha,he,hm⟩ post
    exact ⟨ha,post.1,reg_set l (reg_of pf hm) pf.2.1 pf.2.2 kA post⟩
  -- w = htab_get(lds (bs + 16), addr): read-only
  refine aqmh_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' H0' _ M H => M = M0' ∧ H = H0')
    (RRe := fun _ M0' H0' _ M' H' => H0'.toNat ≤ H'.toNat ∧ M' = M0')
    (Pc := fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      H0.toNat ≤ H.toNat ∧ Reg n c T Out H M) (Qc := fun _ _ _ => True)
    _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp)
    (fun _ M0' H0' _ => aqmh_conseq (aqmh_of_aqm (P := fun H _ M => H = H0' ∧ M = M0')
      (Q := fun H _ _ => H = H0' ∧ True) (RR := fun H _ M => H = H0' ∧ M = M0')
      (fun H _ => aqm_bound_eq (aqm_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
        (by body_check Guest.guestFn_htab_get) (fun _ _ _ hm _ _ _ => hm))))
      (fun L M H ⟨h1,h2⟩ => ⟨h2,h1⟩) (fun _ _ _ _ => trivial) (fun v M H' ⟨H,_,hle,e,r⟩ => by subst e; exact ⟨hle,r⟩))
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => absurd rfl h) ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro L M H v M' H' ⟨⟨A,hA⟩,hle0,pt⟩ ⟨hle,eM⟩ _
    subst eM
    exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,by omega,
      reg_mono pt hle⟩
  -- early return of a block-written account
  refine aqmh_seq (aqmh_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqmh_return _ (fun _ _ _ _ h _ _ => h.1.2.2))
    (aqmh_conseq aqmh_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  -- record the block pre-state read (htab_set on the table at bs + 72)
  refine aqmh_seq (Q := fun _ M H => H0.toNat ≤ H.toNat ∧ Reg n c T Out H M)
    (aqmh_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' H0' _ M H => M = M0' ∧ H = H0')
      (RRe := fun _ M0' H0' _ M' H' => Reg n c T Out H' M' ∧ H0'.toNat ≤ H'.toNat)
      _ _ _ _ _ originalRuntimeCode_recordPreStateRead_lookup (by simp) ?_ (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
      (fun L M H v M' H' ⟨_,hle0,_⟩ ⟨pt,hle⟩ => ⟨by omega,pt⟩)) ?_
  · intro L0 M0' H0' ⟨_,hle0,l',tA',sep',o'⟩
    refine aqmh_conseq (recordPreRead_aqmh Bs hBs (T kB) (l' kB).KL (l' kB).SD (l' kB).C (l' kB).N (l' kB).KS
      (l' kB).VS (l' kB).US (l' kB).OS (l' kB).OPS (l' kB).b H0' (tA' kB).2.1 (o' w hOut kB) (by omega) M0')
      (fun L M H ⟨e1,e2⟩ => by subst e1 e2; exact ⟨hcB ▸ (tA' kB).1,(tA' kB).2.2.1,rfl,rfl⟩)
      (fun _ _ _ _ => trivial) ?_
    intro v M' H' post
    exact ⟨reg_set l' tA' sep' o' kB post,post.1⟩
  -- a = ws_get_account_optional(addr); return a
  refine aqmh_decCallSpec (Vn' := fun x => x ≠ ofString "leaf")
    (Pe := fun _ M0' H0' _ M H => M = M0' ∧ H = H0')
    (RRe := fun _ M0' H0' _ M' H' => H0'.toNat ≤ H'.toNat ∧
      ∀ x, (WsSafe SP0 FM K Pd NB x ∧ x.toNat < H0'.toNat) → M' x = M0' x)
    (Pc := fun _ M H => Reg n c T Out H M) (Qc := fun _ _ _ => True)
    _ _ _ _ _ _ _ originalRuntimeCode_wsGetAccount_lookup (by simp) ?_ (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun _ => rfl) ?_ (aqmh_return _ (fun _ _ _ _ h _ _ => h)) (fun _ _ _ _ _ _ _ _ => trivial)
  · intro L0 M0' H0' ⟨hle0,_⟩
    exact aqmh_conseq (aqmh_of_aqm (P := fun H _ M => H = H0' ∧ M = M0') (Q := fun H _ _ => H = H0' ∧ True)
      (RR := fun H _ M' => H = H0' ∧ ∀ x, (WsSafe SP0 FM K Pd NB x ∧ x.toNat < H0'.toNat) → M' x = M0' x)
      (fun H _ => aqm_bound_eq (aqm_conseq (aqm_frame_of_aq
        (Cond := fun x => WsSafe SP0 FM K Pd NB x ∧ x.toNat < H0'.toNat)
        (fun x hx => wsGetAccount_aq K Pd NB hx.1.1 hx.2 hK0 hPd0 hNB0 hx.1.2.1 hx.1.2.2.1 hx.1.2.2.2)
        ⟨ws,by omega⟩ M0') (fun _ _ h => h) (fun _ _ _ => trivial) (fun _ _ h => h))))
      (fun L M H ⟨h1,h2⟩ => ⟨h2,h1⟩) (fun _ _ _ _ => trivial) (fun v M H' ⟨H,_,hle,e,r⟩ => by subst e; exact ⟨hle,r⟩)
  · intro L M H v M' H' ⟨_,pt⟩ ⟨hle,fr⟩ _
    exact reg_frame (reg_mono pt hle) (fun x hx => fr x ⟨safe x hx,reg_below pt x hx⟩)

#print axioms preStateReg_aqmh

set_option maxHeartbeats 8000000 in
/-- Heap-aware `get_account_optional` over a registry containing the transaction read table (`ts + 8`) and the block
pre-state read table (`bs + 72`): every return re-establishes the registry at the exit heap pointer. -/
theorem accountOptReg_aqmh (n : Nat) (c T : Fin n → BitVec 64) (kA kB : Fin n) (Ts Bs : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (Out : BitVec 64 → Prop) (hOut : Out w)
    (H0 : BitVec 64) (p0 : P0.toNat ≤ H0.toNat) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (ws : WsSafe SP0 FM K Pd NB w) (hp : w.toNat < P0.toNat) :
    AQMH SP0 P0 FM G0 w (fun x => x ≠ ofString "w")
      (fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0 ∧
        Reg n c T Out H0 M)
      (fun _ _ _ => True) (fun _ M' H' => Reg n c T Out H' M')
      (sourceFunctionBody Guest.guestFn_get_account_optional) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_get_account_optional,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  refine aqmh_conseq (P := fun L M H => ∃ l : Fin n → TLay, RegPure n c T Out H0 l ∧
    ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0 ∧ RegMem n c T l M))
    (aqmh_ex (fun l => aqmh_pure_pre (fun pf => ?_)))
    (fun L M H ⟨ha,he,l,tA,sep,o⟩ => ⟨l,⟨fun i => ⟨(tA i).2.1,(tA i).2.2.2⟩,sep,o⟩,ha,he,
      fun i => ⟨(tA i).1,(tA i).2.2.1⟩⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  -- record the transaction read (htab_set on the table at ts + 8)
  refine aqmh_seq (Q := fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      H0.toNat ≤ H.toNat ∧ Reg n c T Out H M)
    (aqmh_setCall (ofString "ts") (by decide) Ts 8 hTs _ _ (T kA) (l kA).KL (l kA).SD (l kA).C (l kA).N (l kA).KS
      (l kA).VS (l kA).US (l kA).OS (l kA).OPS (l kA).b H0 (pf.1 kA).1 (pf.2.2 w hOut kA) p0
      (fun L M H h => ⟨h.2.1,hcA ▸ (h.2.2 kA).1,(h.2.2 kA).2⟩) ?_ ?_) ?_
  · intro F s x H ⟨⟨A,hA⟩,_⟩ _ hx
    rcases hx with hx | hx
    · simp [EV,evalHOLExact,hA] at hx; exact ⟨A,hx.symm⟩
    · simp [EV,evalHOLExact] at hx; exact ⟨1,hx.symm⟩
  · intro L M H M' H' ⟨ha,he,hm⟩ post
    exact ⟨ha,post.1,reg_set l (reg_of pf hm) pf.2.1 pf.2.2 kA post⟩
  -- w = htab_get(lds (ts + 16), addr): read-only
  refine aqmh_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' H0' _ M H => M = M0' ∧ H = H0')
    (RRe := fun _ M0' H0' _ M' H' => H0'.toNat ≤ H'.toNat ∧ M' = M0')
    (Pc := fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      H0.toNat ≤ H.toNat ∧ Reg n c T Out H M) (Qc := fun _ _ _ => True)
    _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp)
    (fun _ M0' H0' _ => aqmh_conseq (aqmh_of_aqm (P := fun H _ M => H = H0' ∧ M = M0')
      (Q := fun H _ _ => H = H0' ∧ True) (RR := fun H _ M => H = H0' ∧ M = M0')
      (fun H _ => aqm_bound_eq (aqm_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
        (by body_check Guest.guestFn_htab_get) (fun _ _ _ hm _ _ _ => hm))))
      (fun L M H ⟨h1,h2⟩ => ⟨h2,h1⟩) (fun _ _ _ _ => trivial) (fun v M H' ⟨H,_,hle,e,r⟩ => by subst e; exact ⟨hle,r⟩))
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => absurd rfl h) ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro L M H v M' H' ⟨⟨A,hA⟩,hle0,pt⟩ ⟨hle,eM⟩ _
    subst eM
    exact ⟨⟨A,by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE,hA]⟩,by omega,
      reg_mono pt hle⟩
  -- early return of a block-written account
  refine aqmh_seq (aqmh_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqmh_return _ (fun _ _ _ _ h _ _ => h.1.2.2))
    (aqmh_conseq aqmh_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  -- a = get_pre_state_account_optional(addr); return a
  refine aqmh_decCallSpec (Vn' := fun x => x ≠ ofString "w")
    (Pe := fun _ _ H0' L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0' ∧
      Reg n c T Out H0' M)
    (RRe := fun _ _ _ _ M' H' => Reg n c T Out H' M')
    (Pc := fun _ M H => Reg n c T Out H M) (Qc := fun _ _ _ => True)
    _ _ _ _ _ _ _ originalRuntimeCode_preStateAccount_lookup (by simp)
    (fun _ _ H0' ⟨_,hle0,_⟩ => by
      have p0' : P0.toNat ≤ H0'.toNat := by omega
      exact preStateReg_aqmh n c T kA kB Ts Bs hTs hBs hcA hcB Out hOut H0' p0' K Pd NB hK0 hPd0 hNB0 safe ws hp)
    ?_ (fun _ => rfl) (fun _ _ _ _ _ _ _ r _ => r) (aqmh_return _ (fun _ _ _ _ h _ _ => h))
    (fun _ _ _ _ _ _ _ _ => trivial)
  intro F s values callee rs _ H _ ⟨⟨A,hA⟩,_,pt⟩ _ args lookup
  rw [evalListHOLFinite_eq_toExact] at args
  simp [evalListHOLExact,evalHOLExact,hA] at args
  subst args
  rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_preStateAccount_lookup] at lookup
  simp only [Option.some.injEq,Prod.mk.injEq] at lookup
  obtain ⟨_,rfl,_⟩ := lookup
  exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,pt⟩

#print axioms accountOptReg_aqmh

theorem source_account_body : sourceFunctionBody Guest.guestFn_get_account =
    .decCall (ofString "a") .one (ofString "get_account_optional") [(.var .local (ofString "addr"))]
      (.seq (.ite (.cmp .equal (.var .local (ofString "a")) (.const 1))
        (.call (some ((some (.local,ofString "a")),none)) (ofString "acct_empty") []) .skip)
      (.return (.var .local (ofString "a")))) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem reg_out_below {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    (h : Reg n c T Out H M) (k : Fin n) (hw : Out w) : w.toNat < H.toNat := by
  obtain ⟨l,_,_,o⟩ := h
  by_contra cc
  exact o w hw k (Or.inr (Or.inr (by omega)))

set_option maxHeartbeats 4000000 in
/-- Heap-aware `get_account(addr)` over the registry: every return re-establishes the registry at the exit heap,
also when an absent account is replaced by a freshly allocated empty account. -/
theorem accountReg_aqmh (n : Nat) (c T : Fin n → BitVec 64) (kA kB : Fin n) (Ts Bs : BitVec 64)
    (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts))) (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs)))
    (hcA : c kA = Ts + 8) (hcB : c kB = Bs + 72) (Out : BitVec 64 → Prop) (hOut : Out w)
    (H0 : BitVec 64) (p0 : P0.toNat ≤ H0.toNat) (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (ws : WsSafe SP0 FM K Pd NB w) (hp : w.toNat < P0.toNat) :
    AQMH SP0 P0 FM G0 w (fun _ => True)
      (fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0 ∧
        Reg n c T Out H0 M)
      (fun _ _ _ => True) (fun _ M' H' => Reg n c T Out H' M')
      (sourceFunctionBody Guest.guestFn_get_account) := by
  rw [source_account_body]
  refine aqmh_decCallSpec (Vn' := fun x => x ≠ ofString "w")
    (Pe := fun _ _ H0' L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0' ∧
      Reg n c T Out H0' M)
    (RRe := fun _ _ _ _ M' H' => Reg n c T Out H' M')
    (Pc := fun _ M H => Reg n c T Out H M) (Qc := fun _ _ _ => True)
    _ _ _ _ _ _ _ originalRuntimeCode_accountOptional_lookup (by simp)
    (fun _ _ H0' ⟨_,e,_⟩ => by
      subst e
      exact accountOptReg_aqmh n c T kA kB Ts Bs hTs hBs hcA hcB Out hOut _ p0 K Pd NB hK0 hPd0 hNB0 safe ws hp)
    ?_ (fun _ => rfl) (fun _ _ _ _ _ _ _ r _ => r) ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro F s values callee rs _ H _ ⟨⟨A,hA⟩,he,pt⟩ _ args lookup
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hA] at args
    subst args he
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_accountOptional_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨A,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,pt⟩
  refine aqmh_seq (Q := fun _ M H => Reg n c T Out H M)
    (aqmh_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
      (fun _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) ?_
      (aqmh_conseq aqmh_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h)))
    (aqmh_return _ (fun _ _ _ _ h _ _ => h))
  refine aqmh_callAssignF (Pe := fun _ M0' H0' _ M H => M = M0' ∧ H = H0')
    (RRe := fun _ M0' H0' v M' H' => (∃ y : BitVec 64, v = .val (.word y)) ∧ H0'.toNat ≤ H'.toNat ∧
      ∀ x : BitVec 64, x.toNat < H0'.toNat → M' x = M0' x)
    _ _ _ _ _ _ originalRuntimeCode_acctEmpty_lookup
    (fun _ M0' H0' ⟨pt,_⟩ => acctEmpty_aqmh M0' H0' (reg_out_below pt kA hOut))
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) ?_
  intro L M H v M' H' ⟨pt,_⟩ ⟨wv,hle,fr⟩
  exact ⟨wv,reg_frame (reg_mono pt hle) (fun x hx => fr x (reg_below pt x hx))⟩

#print axioms accountReg_aqmh
#print axioms reg_set
end InitECandidate.Runtime
