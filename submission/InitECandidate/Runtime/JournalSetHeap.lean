import InitECandidate.Runtime.ArenaHeapGlob
import InitECandidate.Runtime.JournalGlobalKeep
import InitECandidate.Runtime.TableRegistry
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.OriginalTrapCode
import InitECandidate.Runtime.OriginalMemcpyCode
/-!
Heap- and globals-aware original `jset(t, key, value)` on a registry table, using the globals-visible triple `AQG`
with arena predicate `JW` (arena globals plus fixed `journal`, `journal_cap`): the capacity guard's outcome
`journal_n < journal_cap` is carried in the assertions to the four journal-entry stores, the counter is incremented,
and the following `htab_set` re-establishes the whole registry.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {A : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}

theorem aqg_trapCall {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    (k : BitVec 64) : AQG A w Vn P Q RR (.call (some (none,none)) (ofString "trap_with") [.const k]) := by
  intro F s code dom aw sl G hG pre
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [.const k] =
      some [.val (.word k)] := by rw [evalListHOLFinite_eq_toExact]; rfl
  have term := evaluate_trap_call_terminal s (.const k) k code args
  have nr := discard_call_not_returned s (ofString "trap_with") [.const k]
  have lc := discard_call_not_loopControl s (ofString "trap_with") [.const k]
  have mk := memKeep_discardCall (ofString "trap_with") [.const k] _ _ _ originalRuntimeCode_trap_lookup trapWith_memKeep s code
  cases hr : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "trap_with") [.const k]) with
  | mk r t =>
    rw [hr] at term lc mk
    have nr' : ∀ v, r ≠ some (.returned v) := fun v => by have := nr v; rw [hr] at this; exact this
    refine aqg_of_nc (congrFun mk w) ?_
    rintro (h | h | h | ⟨v,h⟩)
    · exact term h
    · exact lc.1 h
    · exact lc.2 h
    · exact nr' v h

/-- A body keeping all globals and writing only inside a window, as a callee spec over any arena predicate. -/
theorem aqg_of_window {Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → Prop} {body : ProgHOL 64}
    (hg : OriginalGlobalsFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (Win : BitVec 64 → Prop)
    (hwin : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → Pe s.locals s.memory →
      ∀ x, ¬ Win x → (evaluateHOLFiniteState s body).2.memory x = s.memory x)
    (hw : ¬ Win w) (M0 : Mem) (G0 : HolFiniteMapExact MlS (ValueHOL 64)) :
    AQG A w (fun _ => False) (fun L M G => Pe L M ∧ M = M0 ∧ G = G0) (fun _ _ _ => True)
      (fun _ M' G' => G' = G0 ∧ ∀ x, ¬ Win x → M' x = M0 x) body := by
  intro F s code dom aw sl G hG ⟨pe,hm,hg0⟩
  unfold GIs at hG
  subst hm hG hg0
  refine ⟨hwin s code pe w hw,fun _ => by rw [hg s code]; exact aw,fun _ => ⟨fun _ h => h.elim,_,rfl,trivial⟩,
    fun v _ => ⟨_,rfl,hg s code,hwin s code pe⟩,evaluate_noTopContinue body nc s,evaluate_noTopBreak body nb s⟩

theorem pair_of_shape {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) (.comb [.one,.one]) = true) :
    ∃ a b : BitVec 64, v = .rStruct [.val (.word a),.val (.word b)] := by
  rcases v with ⟨⟨y⟩⟩ | fs | ⟨n,fs⟩
  · simp [shapeOfHOLExact,shapeEqHOL] at h
  · rcases fs with _ | ⟨f1,_ | ⟨f2,_ | ⟨f3,rest⟩⟩⟩
    · simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at h
    · simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at h
    · rcases f1 with ⟨⟨a⟩⟩ | _ | _ <;> rcases f2 with ⟨⟨b⟩⟩ | _ | _ <;>
        simp_all [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL]
    · simp [shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL] at h
  · simp [shapeOfHOLExact,shapeEqHOL] at h

#print axioms aqg_trapCall
#print axioms aqg_of_window
#print axioms pair_of_shape

variable {SP0 P0 FM : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)}

/-- Arena globals plus fixed journal buffer `journal = J` and capacity `journal_cap = C`. -/
def JW (SP0 P0 FM : BitVec 64) (G0 : HolFiniteMapExact MlS (ValueHOL 64)) (J C : BitVec 64)
    (g : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  AW SP0 P0 FM G0 g ∧ g.lookup (ofString "journal") = some (.val (.word J)) ∧
    g.lookup (ofString "journal_cap") = some (.val (.word C))

/-- Bytes of the journal buffer `[J, J + 32 C)`. -/
def InJ (J C x : BitVec 64) : Prop := J.toNat ≤ x.toNat ∧ x.toNat < J.toNat + C.toNat * 32

/-- Lifting the heap-aware spec of an installed function that keeps the journal globals: the journal counter is
carried from entry to every exit. -/
theorem aqg_of_aqmh_j {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {rs : ShapeHOL}
    (inst : originalRuntimeCode.lookup f = some (params,body,rs)) (gJ : goodJournal f = true)
    (gC : goodJournalCap f = true) (gN : goodJournalN f = true) {J C N : BitVec 64}
    {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop} {RR' : ValueHOL 64 → Mem → BitVec 64 → Prop}
    (h : AQMH SP0 P0 FM G0 w Vn P Q RR' body) :
    AQG (JW SP0 P0 FM G0 J C) w Vn
      (fun L M G => G.lookup (ofString "journal_n") = some (.val (.word N)) ∧ ∃ H, HeapIs G H ∧ P L M H)
      (fun L M G => G.lookup (ofString "journal_n") = some (.val (.word N)) ∧ ∃ H, HeapIs G H ∧ Q L M H)
      (fun v M G => G.lookup (ofString "journal_n") = some (.val (.word N)) ∧ ∃ H, HeapIs G H ∧ RR' v M H) body := by
  have hJ := keepsJournal_of_installed inst gJ
  have hC := keepsJournalCap_of_installed inst gC
  have hN := keepsJournalN_of_installed inst gN
  have h' : AQMG (JW SP0 P0 FM G0 J C) w Vn P Q RR' body :=
    aqmg_strengthen (X := fun g => g.lookup (ofString "journal") = some (.val (.word J)) ∧
        g.lookup (ofString "journal_cap") = some (.val (.word C))) (aqmh_iff_aqmg.mp h)
      (fun s code ⟨x1,x2⟩ => ⟨(evaluate_keeps_journal _ hJ s code).trans x1,
        (evaluate_keeps_journal_cap _ hC s code).trans x2⟩)
  exact aqg_of_aqmg h' (fun G => G.lookup (ofString "journal_n") = some (.val (.word N)))
    (fun s code r => (evaluate_keeps_journal_n _ hN s code).trans r)

#print axioms aqg_of_aqmh_j


/-- Updating `journal_n` keeps the arena globals and the journal globals. -/
theorem jw_update_n {J C : BitVec 64} {g : HolFiniteMapExact MlS (ValueHOL 64)} (h : JW SP0 P0 FM G0 J C g)
    (v : ValueHOL 64) : JW SP0 P0 FM G0 J C (g.update (ofString "journal_n",v)) := by
  obtain ⟨⟨hf,⟨sp,hsp,a1,a2⟩,⟨hp,hhp,b1,b2,b3⟩,st⟩,hj,hc⟩ := h
  have ne : ∀ m : MlS, m ≠ ofString "journal_n" → (g.update (ofString "journal_n",v)).lookup m = g.lookup m :=
    fun m hm => by simp [HolFiniteMapExact.lookup_update,FUPDATE,hm,Ne.symm hm]
  refine ⟨⟨by rw [ne _ (by decide)]; exact hf,⟨sp,by rw [ne _ (by decide)]; exact hsp,a1,a2⟩,
    ⟨hp,by rw [ne _ (by decide)]; exact hhp,b1,b2,b3⟩,fun m hm => ?_⟩,by rw [ne _ (by decide)]; exact hj,
    by rw [ne _ (by decide)]; exact hc⟩
  have : m ≠ ofString "journal_n" := by
    intro e; subst e; revert hm; decide
  rw [ne m this]; exact st m hm

theorem inj_entry {J C Nj o : BitVec 64} (lt : Nj.toNat < C.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496)
    (ho : o.toNat < 32) : InJ J C (J + Nj * 32#64 + o) ∧ (J + Nj * 32#64 + o).toNat = J.toNat + Nj.toNat * 32 + o.toNat := by
  have m : (Nj * 32#64).toNat = Nj.toNat * 32 := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by simp; omega)
  have a1 : (J + Nj * 32#64).toNat = J.toNat + Nj.toNat * 32 := by
    rw [BitVec.toNat_add_of_lt (by rw [m]; omega),m]
  have a2 : (J + Nj * 32#64 + o).toNat = J.toNat + Nj.toNat * 32 + o.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [a1]; omega),a1]
  refine ⟨⟨by rw [a2]; omega,by rw [a2]; omega⟩,a2⟩

/-- Registry facts at a larger heap pointer from layout facts and memory facts. -/
theorem regPure_tabs {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H H' : BitVec 64} {M : Mem}
    {l : Fin n → TLay} (hp : RegPure n c T Out H l) (hm : RegMem n c T l M) (le : H.toNat ≤ H'.toNat) :
    (∀ i, TabAt (c i) (T i) (l i) H' M) ∧ (∀ i j, i ≠ j → TabSep (T i) (l i) (c j) (T j) (l j) H') ∧
      (∀ x, Out x → ∀ i, ¬ (l i).canon (T i) H' x) :=
  ⟨fun i => tabAt_mono (reg_of hp hm i) le,fun i j ne => tabSep_mono (hp.2.1 i j ne) le,
    fun x hx i cc => hp.2.2 x hx i (canon_mono cc le)⟩

/-- Registry cells and headers lie below its heap pointer. -/
theorem regPure_below {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64}
    {l : Fin n → TLay} (hp : RegPure n c T Out H l) (x : BitVec 64) (hx : ∃ i, x = c i ∨ HdrR (T i) x) :
    x.toNat < H.toNat := by
  obtain ⟨i,rfl | ⟨_,hi⟩⟩ := hx
  · by_contra cc; exact (hp.1 i).2 (Or.inr (Or.inr (by omega)))
  · have := (hp.1 i).1.hdrP; omega

/-- Registry memory facts survive any change outside the cells and headers. -/
theorem regMem_frame {n : Nat} {c T : Fin n → BitVec 64} {l : Fin n → TLay} {M M' : Mem}
    (hm : RegMem n c T l M) (fits : ∀ i, (T i).toNat + 72 < 2 ^ 64)
    (keep : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → M' x = M x) : RegMem n c T l M' :=
  fun i => ⟨(keep _ ⟨i,Or.inl rfl⟩).trans (hm i).1,
    hdr_keep (hm i).2 (fits i) (fun x lo hi => keep x ⟨i,Or.inr ⟨lo,hi⟩⟩)⟩

/-- Locals of `jset` after the old-value lookup. -/
def JL (T Kk V : BitVec 64) (L : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  L.lookup (ofString "t") = some (.val (.word T)) ∧ L.lookup (ofString "key") = some (.val (.word Kk)) ∧
    L.lookup (ofString "value") = some (.val (.word V))


/-- `jset` state after the key copy: locals, memory below the entry heap equal to `M0` outside the journal,
counter `Nj < C`, heap at least the entry heap. -/
def JSt (Tk Kk V J C Nj H0 : BitVec 64) (M0 : Mem) (L : HolFiniteMapExact MlS (ValueHOL 64)) (M : Mem)
    (G : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  JL Tk Kk V L ∧ (∃ a b : BitVec 64, L.lookup (ofString "old") = some (.rStruct [.val (.word a),.val (.word b)])) ∧
    (∃ q : BitVec 64, L.lookup (ofString "kc") = some (.val (.word q))) ∧
    (∀ x, x.toNat < H0.toNat → ¬ InJ J C x → M x = M0 x) ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ Nj.toNat < C.toNat ∧
    ∃ H2 : BitVec 64, HeapIs G H2 ∧ H0.toNat ≤ H2.toNat

set_option maxHeartbeats 16000000 in
/-- Heap-aware `jset(t, key, value)` on registry table `k` with journal buffer `[J, J + 32 C)` and counter
`journal_n = Nj`: the watched word (outside the journal, below `P0`, an outside word of the registry) is kept in
every outcome; a return has `Nj < C`, counter `Nj + 1`, the whole registry at the exit heap pointer, and memory
below the entry heap pointer unchanged outside the journal buffer and table `k`'s entry footprint. -/
theorem jset_aqg (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (l : Fin n → TLay) (k : Fin n)
    (H0 : BitVec 64) (pure : RegPure n c T Out H0 l) (Kk V J C Nj : BitVec 64) (M0 : Mem)
    (hm0 : RegMem n c T l M0)
    (p0 : P0.toNat ≤ H0.toNat) (jfit : J.toNat + C.toNat * 32 ≤ 33806089496) (hwJ : ¬ InJ J C w)
    (hwP : w.toNat < P0.toNat) (hOut : Out w)
    (jsep : ∀ x, InJ J C x → ∀ i, x ≠ c i ∧ ¬ HdrR (T i) x) :
    AQG (JW SP0 P0 FM G0 J C) w (fun x => x ≠ ofString "old")
      (fun L M G => JL (T k) Kk V L ∧ RegMem n c T l M ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True)
      (fun _ M' G' => Nj.toNat < C.toNat ∧ G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧
        ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧
          ∀ x, x.toNat < H0.toNat → ¬ InJ J C x → ¬ (l k).canon (T k) H0 x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_jset) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  simp only [Guest.guestFn_jset,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
    Option.map_none]
  -- old = htab_get(t, key): read-only
  refine aqg_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' G0' _ M G => M = M0' ∧ G = G0') (RRe := fun _ M0' G0' _ M' G' => M' = M0' ∧ G' = G0')
    (Pc := fun L M G => JL (T k) Kk V L ∧ (∃ a b : BitVec 64, L.lookup (ofString "old") =
        some (.rStruct [.val (.word a),.val (.word b)])) ∧ RegMem n c T l M ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
    (Qc := fun _ _ _ => True) _ _ _ _ _ _ _ originalRuntimeCode_hashGet_lookup (by simp)
    (fun _ M0' G0' _ => aqg_of_mf htabGet_memoryFrame (by body_check Guest.guestFn_htab_get)
      (by body_check Guest.guestFn_htab_get) M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => absurd rfl h) ?_ ?_ (fun _ _ _ _ _ _ _ _ => trivial)
  · intro L M G v M' G' ⟨⟨ht,hk,hv⟩,rest⟩ ⟨e1,e2⟩ ok
    subst e1 e2
    obtain ⟨a,b,rfl⟩ := pair_of_shape ok
    refine ⟨⟨?_,?_,?_⟩,⟨a,b,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rest⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  -- journal capacity guard
  refine aqg_seq (Q := fun L M G => (JL (T k) Kk V L ∧ (∃ a b : BitVec 64, L.lookup (ofString "old") =
        some (.rStruct [.val (.word a),.val (.word b)])) ∧ RegMem n c T l M ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj))) ∧ Nj.toNat < C.toNat)
    (aqg_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => Nj.toNat < C.toNat) _ ?_ (aqg_trapCall 4)
      (aqg_conseq aqg_skip (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  · intro F s x G ⟨_,_,hcap⟩ hG ⟨_,_,_,_,_,hn⟩ _ ev
    unfold GIs at hG; subst hG
    refine ⟨fun _ => trivial,fun hx => ?_⟩
    subst hx
    simp [EV,evalHOLExact,hn,hcap,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at ev
    exact BitVec.lt_def.mp ev
  have fitT : ∀ i, (T i).toNat + 72 < 2 ^ 64 := fun i => by have := (pure.1 i).1.eEnd; omega
  have hwH0 : w.toNat < H0.toNat := by omega
  -- klen = lds (t + 0): the key length of table k
  refine aqg_dec (Pb := fun L M G => (JL (T k) Kk V L ∧ (∃ a b : BitVec 64, L.lookup (ofString "old") =
        some (.rStruct [.val (.word a),.val (.word b)])) ∧
        L.lookup (ofString "klen") = some (.val (.word (l k).KL))) ∧ RegMem n c T l M ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ Nj.toNat < C.toNat)
    (Qb := fun _ _ _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v G _ hG ⟨⟨⟨ht,hk,hv⟩,⟨a,b,ho⟩,hm,hM,hH,hn⟩,hlt⟩ _ ev _
    rw [ev_load_off s _ (T k) 0#64 v ht ev,(hm k).2.1]
    refine ⟨⟨⟨?_,?_,?_⟩,⟨a,b,?_⟩,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,hm,hM,hH,hn,hlt⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  -- kc = alloc(klen)
  refine aqg_decCallSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' _ L M G => G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H, HeapIs G H ∧
      (L.lookup (ofString "n") = some (.val (.word (l k).KL)) ∧ M = M0' ∧ H = H0))
    (RRe := fun _ M0' _ v M' G' => G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∃ H', HeapIs G' H' ∧
      (M' = M0' ∧ v = .val (.word H0) ∧ H' = allocationEnd H0 (l k).KL ∧ P0.toNat ≤ H0.toNat ∧
        H0.toNat + (l k).KL.toNat ≤ H'.toNat ∧ H'.toNat ≤ 33806089496 ∧ H'.toNat % 8 = 0 ∧ H0.toNat % 8 = 0))
    (Pc := fun L M G => (JL (T k) Kk V L ∧ (∃ a b : BitVec 64, L.lookup (ofString "old") =
        some (.rStruct [.val (.word a),.val (.word b)])) ∧
        L.lookup (ofString "klen") = some (.val (.word (l k).KL)) ∧
        L.lookup (ofString "kc") = some (.val (.word H0))) ∧ M = M0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ Nj.toNat < C.toNat ∧ H0.toNat % 8 = 0 ∧
        ∃ H2 : BitVec 64, HeapIs G H2 ∧ H0.toNat + (l k).KL.toNat ≤ H2.toNat ∧ H2.toNat ≤ 33806089496)
    (Qc := fun _ _ _ => False) _ _ _ _ _ _ _ originalRuntimeCode_allocation_lookup (by simp)
    (fun _ M0' _ _ => aqg_conseq (aqg_of_aqmh_j (J := J) (C := C) (N := Nj) originalRuntimeCode_allocation_lookup
      (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) (l k).KL H0 M0'))
      (fun _ _ _ h => h) (fun _ _ _ _ => trivial) (fun _ _ _ h => h))
    ?_ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s values callee rs _ G hG ⟨⟨_,_,hkl⟩,_,_,hH,hn,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    obtain ⟨x,rfl,ex⟩ := evalList_single s _ values args
    simp [EV,evalHOLExact,hkl] at ex
    subst ex
    rw [pan_single_word_lookup _ _ _ _ _ originalRuntimeCode_allocation_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨hn,H0,hH,by simp [HolFiniteMapExact.lookup_update,FUPDATE],rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨⟨ht,hk,hv⟩,⟨a,b,ho⟩,hkl⟩,_,hM,_,_,hlt⟩ ⟨hn',H',hH',eM,ev,_,_,c1,fin,_,al⟩ _
    subst eM ev
    refine ⟨⟨⟨?_,?_,?_⟩,⟨a,b,?_⟩,?_,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩,hM,hn',hlt,al,H',hH',c1,fin⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  -- memcpy(kc, key, klen): only the fresh key copy changes
  refine aqg_seq (Q := fun L M G => JSt (T k) Kk V J C Nj H0 M0 L M G)
    (aqg_callSpec (Vn' := fun _ => False)
      (Pe := fun _ M0' G0' L M G => (L.lookup (ofString "dst") = some (.val (.word H0)) ∧
        L.lookup (ofString "src") = some (.val (.word Kk)) ∧
        L.lookup (ofString "n") = some (.val (.word (l k).KL))) ∧ M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' _ M' G' => G' = G0' ∧ ∀ x, ¬ MWin H0 (l k).KL.toNat x → M' x = M0' x)
      _ _ _ _ _ originalRuntimeCode_memcpy_lookup (by simp) ?_ ?_ ?_) ?_
  · intro L0 M0' G0' ⟨_,_,_,_,al,H2,_,c1,fin⟩
    have small : (l k).KL.toNat + 32 < 2 ^ 64 := by omega
    exact aqg_of_window memcpy_body_globals_frame (by body_check Guest.guestFn_memcpy)
      (by body_check Guest.guestFn_memcpy) (MWin H0 (l k).KL.toNat)
      (fun s _ ⟨hd,hs,hn⟩ x hx => memcpy_body_window s H0 Kk (l k).KL x hd hs hn small hx)
      (mwin_above hwH0 al (by omega)) M0' G0'
  · intro F s values callee rs _ G hG ⟨⟨⟨ht,hk,hv⟩,_,hkl,hkc⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,hkc,hk,hkl] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_memcpy_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    exact ⟨⟨by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE],
      by simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]⟩,rfl,rfl⟩
  · intro L M G v M' G' ⟨⟨hjl,hold,_,hkc⟩,hM,hn,hlt,al,H2,hH2,c1,fin⟩ ⟨eG,fr⟩
    subst eG hM
    refine ⟨hjl,hold,⟨H0,hkc⟩,fun x hx _ => fr x (fun hw' => ?_),hn,hlt,H2,hH2,by omega⟩
    have := (mwin_ge hw' al (by omega)).1
    omega
  -- r = journal + journal_n * 32
  refine aqg_dec (Pb := fun L M G => JSt (T k) Kk V J C Nj H0 M0 L M G ∧
      L.lookup (ofString "r") = some (.val (.word (J + Nj * 32#64))))
    (Qb := fun _ _ _ => False) _ _ _ (fun _ => rfl) ?_ ?_ (fun _ _ _ _ _ _ _ h => h.elim)
  · intro F s v G aw hG ⟨⟨ht,hk,hv⟩,⟨a,b,ho⟩,⟨q,hq⟩,fr,hn,hlt,hH⟩ _ ev _
    unfold GIs at hG; subst hG
    have hj := aw.2.1
    simp [EV,evalHOLExact,evalListHOLExact,hj,hn,panOpHOL,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    refine ⟨⟨⟨?_,?_,?_⟩,⟨a,b,?_⟩,⟨q,?_⟩,fr,hn,hlt,hH⟩,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩ <;>
      simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  -- the journal entry: four word stores inside [J + 32 Nj, J + 32 Nj + 32)
  have jst : ∀ (d v : ExpHOL 64) (o : BitVec 64), o.toNat < 32 →
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
        s.locals.lookup (ofString "r") = some (.val (.word (J + Nj * 32#64))) →
        EV s d = some (.val (.word (J + Nj * 32#64 + o)))) →
      (∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, JSt (T k) Kk V J C Nj H0 M0 s.locals s.memory s.globals →
        EV s v = some x → ∃ y : BitVec 64, x = .val (.word y)) →
      AQG (JW SP0 P0 FM G0 J C) w (fun x => x ≠ ofString "old")
        (fun L M G => JSt (T k) Kk V J C Nj H0 M0 L M G ∧
          L.lookup (ofString "r") = some (.val (.word (J + Nj * 32#64))))
        (fun L M G => JSt (T k) Kk V J C Nj H0 M0 L M G ∧
          L.lookup (ofString "r") = some (.val (.word (J + Nj * 32#64))))
        (fun _ M' G' => Nj.toNat < C.toNat ∧ G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧
          ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧
            ∀ x, x.toNat < H0.toNat → ¬ InJ J C x → ¬ (l k).canon (T k) H0 x → M' x = M0 x)
        (.store d v) := by
    intro d v o ho hd hv
    refine aqg_store _ _ (fun s G _ hG ⟨st,hr⟩ _ => ?_) (fun s x G _ hG ⟨st,_⟩ _ ev => ?_)
    · unfold GIs at hG; subst hG
      obtain ⟨hjl,hold,hkc,fr,hn,hlt,hH⟩ := st
      obtain ⟨inj,_⟩ := inj_entry (o := o) hlt jfit ho
      refine ⟨_,hd s hr,fun e => hwJ (e ▸ inj),fun y _ => ⟨⟨hjl,hold,hkc,fun x hx hnj => ?_,hn,hlt,hH⟩,hr⟩⟩
      have : x ≠ J + Nj * 32#64 + o := fun e => hnj (e ▸ inj)
      simp only [if_neg this]
      exact fr x hx hnj
    · unfold GIs at hG; subst hG
      exact hv s x st ev
  refine aqg_seq (jst _ _ 0#64 (by decide) (fun s hr => by simp [EV,evalHOLExact,hr])
    (fun s x ⟨⟨ht,_,_⟩,_⟩ ev => by simp [EV,evalHOLExact,ht] at ev; exact ⟨_,ev.symm⟩)) ?_
  refine aqg_seq (jst _ _ 8#64 (by decide)
    (fun s hr => by simp [EV,evalHOLExact,evalListHOLExact,hr,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨_,_,⟨q,hq⟩,_⟩ ev => by simp [EV,evalHOLExact,hq] at ev; exact ⟨_,ev.symm⟩)) ?_
  refine aqg_seq (jst _ _ 16#64 (by decide)
    (fun s hr => by simp [EV,evalHOLExact,evalListHOLExact,hr,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨_,⟨a,b,ho⟩,_⟩ ev => by simp [EV,evalHOLExact,ho] at ev; exact ⟨_,ev.symm⟩)) ?_
  refine aqg_seq (jst _ _ 24#64 (by decide)
    (fun s hr => by simp [EV,evalHOLExact,evalListHOLExact,hr,wordOpHOL,wordOp,valueIsWord,valueWord])
    (fun s x ⟨_,⟨a,b,ho⟩,_⟩ ev => by simp [EV,evalHOLExact,ho] at ev; exact ⟨_,ev.symm⟩)) ?_
  -- journal_n = journal_n + 1
  refine aqg_seq (Q := fun L M G => JL (T k) Kk V L ∧ (∀ x, x.toNat < H0.toNat → ¬ InJ J C x → M x = M0 x) ∧
      G.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧ Nj.toNat < C.toNat ∧
      ∃ H2 : BitVec 64, HeapIs G H2 ∧ H0.toNat ≤ H2.toNat)
    (aqg_assignGlobal _ _ (fun s v aw ⟨⟨hjl,_,_,fr,hn,hlt,H2,hH2,hle⟩,_⟩ _ ev => ?_)) ?_
  · simp [EV,evalHOLExact,evalListHOLExact,hn,wordOpHOL,wordOp,valueIsWord,valueWord] at ev
    subst ev
    refine ⟨jw_update_n aw _,hjl,fr,by simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE],hlt,H2,?_,hle⟩
    have ne : ofString "journal_n" ≠ ofString "heap_ptr" := by decide
    unfold HeapIs at hH2 ⊢
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,ne,hH2]
  -- htab_set(t, key, value) on table k, rebound to the current heap pointer
  refine aqg_seq (Q := fun _ M' G' => Nj.toNat < C.toNat ∧
      G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧
      ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ Reg n c T Out H' M' ∧
        ∀ x, x.toNat < H0.toNat → ¬ InJ J C x → ¬ (l k).canon (T k) H0 x → M' x = M0 x)
    (aqg_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' G0' L M G => LK (irP0 (T k) Kk V) L ∧ M = M0' ∧ G = G0')
      (RRe := fun _ M0' G0' _ M' G' => G'.lookup (ofString "journal_n") = some (.val (.word (Nj + 1))) ∧
        ∃ H2 H' : BitVec 64, HeapIs G0' H2 ∧ H0.toNat ≤ H2.toNat ∧ HeapIs G' H' ∧
          SetPost (T k) ((l k).canon (T k) H2) M0' (l k).C (l k).SD (l k).KS (l k).VS (l k).US (l k).OS (l k).OPS
            H2 M' H')
      _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ ?_)
    (aqg_return _ (fun _ _ _ _ _ h _ _ => h))
  · intro L0 M0' G0' ⟨_,fr,hn1,_,H2,hH2,hle⟩
    have hm : RegMem n c T l M0' := regMem_frame hm0 fitT (fun x hx => fr x (regPure_below pure x hx)
      (fun hj => by obtain ⟨i,hi⟩ := hx; rcases hi with rfl | hi
                    · exact (jsep _ hj i).1 rfl
                    · exact (jsep _ hj i).2 hi))
    have lay := hlay_canon (pure.1 k).1 hle
    have hwk : ¬ (l k).canon (T k) H2 w := fun cc => pure.2.2 w hOut k (canon_mono cc hle)
    have p2 : P0.toNat ≤ H2.toNat := by omega
    refine aqg_conseq (aqg_of_aqmh_j (J := J) (C := C) (N := Nj + 1) originalRuntimeCode_hashSet_lookup
      (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (aqmh_rebound (set_aqmh (P0 := H2) (T k) Kk V _ (l k).KL (l k).SD (l k).C (l k).N (l k).KS (l k).VS (l k).US
        (l k).OS (l k).OPS (l k).b lay M0' hwk H2 (le_refl _)) p2))
      ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hl,hM,hG⟩
      subst hM hG
      exact ⟨hn1,H2,hH2,le_refl _,hl,(hm k).2,rfl,rfl⟩
    · intro v M' G' ⟨hn',H',hH',post⟩
      exact ⟨hn',H2,H',hH2,hle,hH',post⟩
  · intro F s values callee rs _ G hG ⟨⟨ht,hk,hv⟩,_⟩ _ args lookup
    unfold GIs at hG; subst hG
    rw [evalListHOLFinite_eq_toExact] at args
    simp [evalListHOLExact,evalHOLExact,ht,hk,hv] at args
    subst args
    rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      originalRuntimeCode_hashSet_lookup] at lookup
    simp only [Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨_,rfl,_⟩ := lookup
    refine ⟨fun p hp => ?_,rfl,rfl⟩
    simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · intro L M G v M' G' ⟨_,fr,_,hlt,H2,hH2,hle⟩ ⟨hn',H2',H',hG2,_,hH',post⟩
    have e : H2' = H2 := by
      unfold HeapIs at hH2 hG2; rw [hH2] at hG2; simpa using hG2.symm
    subst e
    have hm : RegMem n c T l M := regMem_frame hm0 fitT (fun x hx => fr x (regPure_below pure x hx)
      (fun hj => by obtain ⟨i,hi⟩ := hx; rcases hi with rfl | hi
                    · exact (jsep _ hj i).1 rfl
                    · exact (jsep _ hj i).2 hi))
    obtain ⟨tA,sep,o⟩ := regPure_tabs pure hm hle
    refine ⟨hlt,hn',H',hH',le_trans hle post.1,reg_set l tA sep o k post,fun x hx hnj hnc => ?_⟩
    exact (post.2.1 x (fun cc => hnc (canon_mono cc hle))).trans (fr x hx hnj)

#print axioms jw_update_n
#print axioms inj_entry
#print axioms jset_aqg
end InitECandidate.Runtime
