import InitECandidate.Runtime.HtabSetHeap
import InitECandidate.Runtime.PreStateAccountArena
/-!
Heap-aware `get_pre_state_account_optional` with both read tables.  `PreTabs` is the two-table invariant at a heap
pointer: the transaction read table (cell `ts + 8`) and the block pre-state read table (cell `bs + 72`) are each
valid against their canonical footprints (header, own arrays, heap above the pointer) with headers in memory and
mutually separated.  `preState_aqmh` shows it is re-established at the exit heap pointer of every return, so it
carries from one call to the next.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)} {Vn : MlS → Prop}


/-- A table layout's header fields (key length, stride, capacity, count, five array pointers) and log capacity. -/
structure TLay where
  KL : BitVec 64
  SD : BitVec 64
  C : BitVec 64
  N : BitVec 64
  KS : BitVec 64
  VS : BitVec 64
  US : BitVec 64
  OS : BitVec 64
  OPS : BitVec 64
  b : Nat

namespace TLay
/-- Canonical footprint of table `T` with layout `l` at heap pointer `H`. -/
def canon (l : TLay) (T H : BitVec 64) : BitVec 64 → Prop := Canon T l.C l.SD l.KS l.VS l.US l.OS l.OPS H
def arr (l : TLay) : BitVec 64 → Prop := ArrOf l.C l.SD l.KS l.VS l.US l.OS l.OPS
/-- Valid against its canonical footprint at heap pointer `H`. -/
def ok (l : TLay) (T H : BitVec 64) : Prop := HLay H T (l.canon T H) l.KL l.SD l.C l.N l.KS l.VS l.US l.OS l.OPS l.b
def hdr (l : TLay) (M : Mem) (T : BitVec 64) : Prop := Hdr M T l.KL l.SD l.C l.N l.KS l.VS l.US l.OS l.OPS
end TLay

/-- Header bytes of table `T`. -/
def HdrR (T x : BitVec 64) : Prop := T.toNat ≤ x.toNat ∧ x.toNat < T.toNat + 72

/-- One table at heap pointer `H`: its pointer cell `c` holds `T`, its layout is valid against its canonical
footprint and its header is in memory; the pointer cell lies outside its own footprint. -/
def TabAt (c T : BitVec 64) (l : TLay) (H : BitVec 64) (M : Mem) : Prop :=
  M c = .word T ∧ l.ok T H ∧ l.hdr M T ∧ ¬ l.canon T H c

/-- Table `Y` (cell, header, arrays) lies outside table `X`'s canonical footprint at `H`. -/
def TabSep (TX : BitVec 64) (lX : TLay) (cY TY : BitVec 64) (lY : TLay) (H : BitVec 64) : Prop :=
  ∀ x, (x = cY ∨ HdrR TY x ∨ lY.arr x) → ¬ lX.canon TX H x

theorem canon_mono {T C SD KS VS US OS OPS H H' x : BitVec 64} (h : Canon T C SD KS VS US OS OPS H' x)
    (le : H.toNat ≤ H'.toNat) : Canon T C SD KS VS US OS OPS H x := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by omega))

theorem tabAt_mono {c T : BitVec 64} {l : TLay} {H H' : BitVec 64} {M : Mem} (h : TabAt c T l H M)
    (le : H.toNat ≤ H'.toNat) : TabAt c T l H' M :=
  ⟨h.1,hlay_canon h.2.1 le,h.2.2.1,fun hc => h.2.2.2 (canon_mono hc le)⟩

theorem tabSep_mono {TX : BitVec 64} {lX : TLay} {cY TY : BitVec 64} {lY : TLay} {H H' : BitVec 64}
    (h : TabSep TX lX cY TY lY H) (le : H.toNat ≤ H'.toNat) : TabSep TX lX cY TY lY H' :=
  fun x hx hc => h x hx (canon_mono hc le)

/-- A set on table `X` (started at heap pointer `H`, footprint `lX.canon TX H`) keeps a separated table `Y`
and the separation in both directions, at the exit heap pointer `H'`, with `X`'s new layout. -/
theorem set_sep {cX TX cY TY : BitVec 64} {lX lY : TLay} {H H' : BitVec 64} {M M' : Mem}
    (tX : TabAt cX TX lX H M) (tY : TabAt cY TY lY H M)
    (sXY : TabSep TX lX cY TY lY H) (sYX : TabSep TY lY cX TX lX H)
    (post : SetPost TX (lX.canon TX H) M lX.C lX.SD lX.KS lX.VS lX.US lX.OS lX.OPS H M' H') :
    ∃ lX' : TLay, TabAt cX TX lX' H' M' ∧ TabAt cY TY lY H' M' ∧ TabSep TX lX' cY TY lY H' ∧
      TabSep TY lY cX TX lX' H' ∧ H.toNat ≤ H'.toNat ∧ (∀ x, ¬ lX.canon TX H x → M' x = M x) ∧
      (∀ x, ¬ lX.canon TX H x → ¬ lX'.canon TX H' x) := by
  obtain ⟨hle,ag,KL',SD',C',N',KS',VS',US',OS',OPS',b',hlay',hdr',inn⟩ := post
  let lX' : TLay := ⟨KL',SD',C',N',KS',VS',US',OS',OPS',b'⟩
  -- anything outside X's old footprint stays outside X's new footprint
  have keepOut : ∀ x, ¬ lX.canon TX H x → ¬ lX'.canon TX H' x := by
    intro x hx hc
    rcases hc with h | h | h
    · exact hx (Or.inl h)
    · rcases inn x h with h' | ⟨lo,_⟩
      · exact hx (Or.inr (Or.inl h'))
      · exact hx (Or.inr (Or.inr lo))
    · exact hx (Or.inr (Or.inr (by omega)))
  have fitY : TY.toNat + 72 < 2 ^ 64 := by have := tY.2.1.eEnd; omega
  refine ⟨lX',⟨(ag _ tX.2.2.2).trans tX.1,hlay',hdr',keepOut _ tX.2.2.2⟩,
    ⟨(ag _ (sXY _ (Or.inl rfl))).trans tY.1,hlay_canon tY.2.1 hle,
      hdr_keep tY.2.2.1 fitY (fun x lo hi => ag x (sXY x (Or.inr (Or.inl ⟨lo,hi⟩)))),
      fun hc => tY.2.2.2 (canon_mono hc hle)⟩,
    fun x hx => keepOut x (sXY x hx),?_,hle,ag,keepOut⟩
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


/-- A heap-aware triple at a higher arena bound `Q` holds at bound `P0 ≤ Q` from any heap pointer at least `Q`. -/
theorem aqmh_rebound {Q : BitVec 64} {P Qp : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop}
    {RR : ValueHOL 64 → Mem → BitVec 64 → Prop} {p : ProgHOL 64}
    (h : AQMH SP0 Q FM G0 w Vn P Qp RR p) (le : P0.toNat ≤ Q.toNat) :
    AQMH SP0 P0 FM G0 w Vn (fun L M H => Q.toNat ≤ H.toNat ∧ P L M H) Qp RR p := by
  intro F s code dom aw sl H hH ⟨hq,pre⟩
  have awQ : AW SP0 Q FM G0 s.globals := by
    obtain ⟨hf,hs,⟨h',hh,_,hi,al⟩,st⟩ := aw
    have e : h' = H := by unfold HeapIs at hH; rw [hh] at hH; simpa using hH
    subst e
    exact ⟨hf,hs,⟨h',hh,hq,hi,al⟩,st⟩
  obtain ⟨m,a,n,r,c,b⟩ := h F s code dom awQ sl H hH pre
  exact ⟨m,fun cont => (aw_lower (a cont) le).1,n,r,c,b⟩

/-- An arena triple holding for every watched word satisfying `Cond` gives a memory-aware frame: every such word is
kept on a return or a normal exit. -/
theorem aqm_frame_of_aq {Cond : BitVec 64 → Prop} {Q' : HolFiniteMapExact MlS (ValueHOL 64) → Prop} {p : ProgHOL 64}
    (h : ∀ x, Cond x → AQ SP0 P0 FM G0 x Vn (fun _ => True) Q' p) (hw : Cond w) (M0 : Mem) :
    AQM SP0 P0 FM G0 w Vn (fun _ M => M = M0) (fun _ M' => ∀ x, Cond x → M' x = M0 x)
      (fun _ M' => ∀ x, Cond x → M' x = M0 x) p := by
  intro F s code dom aw sl pre
  subst pre
  obtain ⟨m,a,n,c,b⟩ := h w hw F s code dom aw sl trivial
  exact ⟨m,a,fun e => ⟨(n e).1,fun x hx => (h x hx F s code dom aw sl trivial).1⟩,
    fun _ _ x hx => (h x hx F s code dom aw sl trivial).1,c,b⟩

/-- Words `ws_get_account_optional` never writes (besides the arena bound): outside the scratch arena and the
Keccak/nibble buffers. -/
def WsSafe (SP0 FM K Pd NB : BitVec 64) (x : BitVec 64) : Prop :=
  (x.toNat < FM.toNat ∨ SP0.toNat ≤ x.toNat) ∧ ¬ MWin K 200 x ∧ ¬ MWin Pd 136 x ∧
    ∀ j : Nat, j < 64 → x ≠ panByteAlignHOL (NB + BitVec.ofNat 64 j)


/-- `htab_set(lds (g + off), a2, a3)` from heap pointer `H0` on a table (pointer in a static global's record)
valid against its canonical footprint at `H0`. -/
theorem aqmh_setCall {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop}
    {RR : ValueHOL 64 → Mem → BitVec 64 → Prop} (g : MlS) (hg : g ∈ staticGlobalNames)
    (Gv off : BitVec 64) (hG0 : G0.lookup g = some (.val (.word Gv))) (a2 a3 : ExpHOL 64)
    (T KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat) (H0 : BitVec 64)
    (lay : HLay H0 T (Canon T C SD KS VS US OS OPS H0) KL SD C N KS VS US OS OPS b)
    (hw : ¬ Canon T C SD KS VS US OS OPS H0 w) (p0 : P0.toNat ≤ H0.toNat)
    (hP : ∀ L M H, P L M H → H = H0 ∧ M (Gv + off) = .word T ∧ Hdr M T KL SD C N KS VS US OS OPS)
    (hargs : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x H, P s.locals s.memory H → SL Vn s.locals →
      (EV s a2 = some x ∨ EV s a3 = some x) → ∃ y : BitVec 64, x = .val (.word y))
    (hq : ∀ L M H M' H', P L M H → SetPost T (Canon T C SD KS VS US OS OPS H0) M C SD KS VS US OS OPS H0 M' H' →
      Q L M' H') :
    AQMH SP0 P0 FM G0 w Vn P Q RR
      (.call (some (none,none)) (ofString "htab_set") [.load .one (.op .add [.var .global g,.const off]),a2,a3]) := by
  refine aqmh_callSpec (Vn' := fun _ => True)
    (Pe := fun _ M0' H0' L M H => (∃ Kk V : BitVec 64, LK (irP0 T Kk V) L) ∧ Hdr M T KL SD C N KS VS US OS OPS ∧
      M = M0' ∧ H = H0')
    (RRe := fun _ M0' _ _ M' H' => SetPost T (Canon T C SD KS VS US OS OPS H0) M0' C SD KS VS US OS OPS H0 M' H')
    _ _ _ _ _ originalRuntimeCode_hashSet_lookup (by simp) ?_ ?_ (fun L M H v M' H' h h' => hq L M H M' H' h h')
  · intro L0 M0' H0' hp F s code dom aw sl H hH ⟨⟨Kk,V,hl⟩,hh,hm,he⟩
    have e0 := (hP _ _ _ hp).1
    subst e0 he
    exact aqmh_rebound (set_aqmh (P0 := H) T Kk V _ KL SD C N KS VS US OS OPS b lay M0' hw H (le_refl _)) p0
      F s code dom aw sl H hH ⟨le_refl _,hl,hh,hm,rfl⟩
  · intro F s values callee rs aw H _ pre sl args lookup
    obtain ⟨_,hcell,hh⟩ := hP _ _ _ pre
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
          obtain ⟨y2,rfl⟩ := hargs s x2 H pre sl (Or.inl h2)
          obtain ⟨y3,rfl⟩ := hargs s x3 H pre sl (Or.inr h3)
          simp [evalListHOLExact,h1,h2,h3] at args
          subst args
          rw [pan_three_word_lookup _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
            originalRuntimeCode_hashSet_lookup] at lookup
          simp only [Option.some.injEq,Prod.mk.injEq] at lookup
          obtain ⟨_,rfl,_⟩ := lookup
          refine ⟨⟨y2,y3,fun p hp => ?_⟩,hh,rfl,rfl⟩
          simp only [irP0,List.mem_cons,List.mem_nil_iff,or_false] at hp
          rcases hp with rfl | rfl | rfl <;> simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]

/-- Heap-aware `record_pre_state_read(addr)` from heap pointer `H0` on the block pre-state read table. -/
theorem recordPreRead_aqmh (Bv : BitVec 64) (hG0 : G0.lookup (ofString "bs") = some (.val (.word Bv)))
    (T KL SD C N KS VS US OS OPS : BitVec 64) (b : Nat) (H0 : BitVec 64)
    (lay : HLay H0 T (Canon T C SD KS VS US OS OPS H0) KL SD C N KS VS US OS OPS b)
    (hw : ¬ Canon T C SD KS VS US OS OPS H0 w) (p0 : P0.toNat ≤ H0.toNat) (M0 : Mem) :
    AQMH SP0 P0 FM G0 w (fun _ => True)
      (fun _ M H => M (Bv + 72) = .word T ∧ Hdr M T KL SD C N KS VS US OS OPS ∧ M = M0 ∧ H = H0)
      (fun _ _ _ => True)
      (fun _ M' H' => SetPost T (Canon T C SD KS VS US OS OPS H0) M0 C SD KS VS US OS OPS H0 M' H')
      (sourceFunctionBody Guest.guestFn_record_pre_state_read) := by
  rw [source_recordPreRead_body]
  refine aqmh_seq (Q := fun _ M H => SetPost T (Canon T C SD KS VS US OS OPS H0) M0 C SD KS VS US OS OPS H0 M H)
    (aqmh_setCall (ofString "bs") (by decide) Bv 72 hG0 _ _ T KL SD C N KS VS US OS OPS b H0 lay hw p0
      (fun L M H h => ⟨h.2.2.2,h.1,h.2.1⟩) ?_ ?_) (aqmh_return _ (fun _ _ _ _ h _ _ => h))
  · intro F s x H _ sl hx
    rcases hx with hx | hx
    · simp [EV,evalHOLExact] at hx
      exact sl _ trivial x hx
    · simp [EV,evalHOLExact] at hx
      exact ⟨1,hx.symm⟩
  · intro L M H M' H' ⟨_,_,hm,_⟩ h
    subst hm; exact h

#print axioms aqmh_setCall
#print axioms recordPreRead_aqmh

theorem aqmh_ex {α : Type} {P : α → HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop}
    {Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop} {RR : ValueHOL 64 → Mem → BitVec 64 → Prop}
    {p : ProgHOL 64} (h : ∀ a, AQMH SP0 P0 FM G0 w Vn (P a) Q RR p) :
    AQMH SP0 P0 FM G0 w Vn (fun L M H => ∃ a, P a L M H) Q RR p :=
  fun F s code dom aw sl H hH ⟨a,pre⟩ => h a F s code dom aw sl H hH pre

theorem aqmh_pure_pre {φ : Prop} {P Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop}
    {RR : ValueHOL 64 → Mem → BitVec 64 → Prop} {p : ProgHOL 64} (h : φ → AQMH SP0 P0 FM G0 w Vn P Q RR p) :
    AQMH SP0 P0 FM G0 w Vn (fun L M H => φ ∧ P L M H) Q RR p :=
  fun F s code dom aw sl H hH ⟨f,pre⟩ => h f F s code dom aw sl H hH pre

theorem aqmh_skip {P : HolFiniteMapExact MlS (ValueHOL 64) → Mem → BitVec 64 → Prop}
    {RR : ValueHOL 64 → Mem → BitVec 64 → Prop} : AQMH SP0 P0 FM G0 w Vn P P RR .skip := by
  intro F s code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_skip]
  exact ⟨rfl,fun _ => aw,fun _ => ⟨sl,H,hH,pre⟩,(fun v e => by cases e),by simp,by simp⟩

/-- The two read tables at heap pointer `H`: the transaction read table (pointer cell `Ts + 8`, header `Ta`) and the
block pre-state read table (pointer cell `Bs + 72`, header `Tb`), each valid against its canonical footprint with
its header in memory, mutually separated (cell, header and arrays of each outside the other's footprint), and the
words `Out` outside both footprints. -/
def PreTabs (Ts Bs Ta Tb : BitVec 64) (Out : BitVec 64 → Prop) (H : BitVec 64) (M : Mem) : Prop :=
  ∃ lA lB : TLay, TabAt (Ts + 8) Ta lA H M ∧ TabAt (Bs + 72) Tb lB H M ∧ TabSep Ta lA (Bs + 72) Tb lB H ∧
    TabSep Tb lB (Ts + 8) Ta lA H ∧ ∀ x, Out x → ¬ lA.canon Ta H x ∧ ¬ lB.canon Tb H x

theorem preTabs_mono {Ts Bs Ta Tb : BitVec 64} {Out : BitVec 64 → Prop} {H H' : BitVec 64} {M : Mem}
    (h : PreTabs Ts Bs Ta Tb Out H M) (le : H.toNat ≤ H'.toNat) : PreTabs Ts Bs Ta Tb Out H' M := by
  obtain ⟨lA,lB,tA,tB,sAB,sBA,o⟩ := h
  exact ⟨lA,lB,tabAt_mono tA le,tabAt_mono tB le,tabSep_mono sAB le,tabSep_mono sBA le,
    fun x hx => ⟨fun c => (o x hx).1 (canon_mono c le),fun c => (o x hx).2 (canon_mono c le)⟩⟩

/-- The tables' cells and headers lie below the heap pointer. -/
theorem preTabs_below {Ts Bs Ta Tb : BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    (h : PreTabs Ts Bs Ta Tb Out H M) (x : BitVec 64) (hx : x = Ts + 8 ∨ x = Bs + 72 ∨ HdrR Ta x ∨ HdrR Tb x) :
    x.toNat < H.toNat := by
  obtain ⟨lA,lB,tA,tB,_,_,_⟩ := h
  rcases hx with rfl | rfl | ⟨_,hi⟩ | ⟨_,hi⟩
  · by_contra c; exact tA.2.2.2 (Or.inr (Or.inr (by omega)))
  · by_contra c; exact tB.2.2.2 (Or.inr (Or.inr (by omega)))
  · have := tA.2.1.hdrP; omega
  · have := tB.2.1.hdrP; omega

/-- The two read tables only depend on their cells' and headers' words. -/
theorem preTabs_frame {Ts Bs Ta Tb : BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M M' : Mem}
    (h : PreTabs Ts Bs Ta Tb Out H M)
    (keep : ∀ x, (x = Ts + 8 ∨ x = Bs + 72 ∨ HdrR Ta x ∨ HdrR Tb x) → M' x = M x) :
    PreTabs Ts Bs Ta Tb Out H M' := by
  obtain ⟨lA,lB,tA,tB,sAB,sBA,o⟩ := h
  have fA : Ta.toNat + 72 < 2 ^ 64 := by have := tA.2.1.eEnd; omega
  have fB : Tb.toNat + 72 < 2 ^ 64 := by have := tB.2.1.eEnd; omega
  exact ⟨lA,lB,⟨(keep _ (Or.inl rfl)).trans tA.1,tA.2.1,
      hdr_keep tA.2.2.1 fA (fun x lo hi => keep x (Or.inr (Or.inr (Or.inl ⟨lo,hi⟩)))),tA.2.2.2⟩,
    ⟨(keep _ (Or.inr (Or.inl rfl))).trans tB.1,tB.2.1,
      hdr_keep tB.2.2.1 fB (fun x lo hi => keep x (Or.inr (Or.inr (Or.inr ⟨lo,hi⟩)))),tB.2.2.2⟩,sAB,sBA,o⟩

set_option maxHeartbeats 8000000 in
/-- Heap-aware `get_pre_state_account_optional` from heap pointer `H0` with both read tables valid against their
canonical footprints and mutually separated: the watched word (outside both footprints, below `P0`, outside the
scratch arena and the Keccak/nibble buffers) is kept in every outcome, and every return leaves both read tables
valid, separated and in memory at the exit heap pointer, the watched word still outside both footprints.  The
cells and headers must avoid the scratch arena and the Keccak/nibble buffers. -/
theorem preState_aqmh (Ts Bs : BitVec 64) (hTs : G0.lookup (ofString "ts") = some (.val (.word Ts)))
    (hBs : G0.lookup (ofString "bs") = some (.val (.word Bs))) (Ta Tb H0 : BitVec 64) (p0 : P0.toNat ≤ H0.toNat)
    (K Pd NB : BitVec 64)
    (hK0 : G0.lookup (ofString "keccak_st") = some (.val (.word K)))
    (hPd0 : G0.lookup (ofString "keccak_pad") = some (.val (.word Pd)))
    (hNB0 : G0.lookup (ofString "mpt_nib_scratch") = some (.val (.word NB)))
    (safe : ∀ x, (x = Ts + 8 ∨ x = Bs + 72 ∨ HdrR Ta x ∨ HdrR Tb x) → WsSafe SP0 FM K Pd NB x)
    (ws : WsSafe SP0 FM K Pd NB w) (hp : w.toNat < P0.toNat) :
    AQMH SP0 P0 FM G0 w (fun x => x ≠ ofString "w")
      (fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0 ∧
        PreTabs Ts Bs Ta Tb (fun x => x = w) H0 M)
      (fun _ _ _ => True) (fun _ M' H' => PreTabs Ts Bs Ta Tb (fun x => x = w) H' M')
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
  refine aqmh_conseq (P := fun L M H => ∃ l : TLay × TLay,
    (l.1.ok Ta H0 ∧ ¬ l.1.canon Ta H0 (Ts + 8) ∧ l.2.ok Tb H0 ∧ ¬ l.2.canon Tb H0 (Bs + 72) ∧
      TabSep Ta l.1 (Bs + 72) Tb l.2 H0 ∧ TabSep Tb l.2 (Ts + 8) Ta l.1 H0 ∧
      ¬ l.1.canon Ta H0 w ∧ ¬ l.2.canon Tb H0 w) ∧
    ((∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧ H = H0 ∧
      M (Ts + 8) = .word Ta ∧ l.1.hdr M Ta ∧ M (Bs + 72) = .word Tb ∧ l.2.hdr M Tb))
    (aqmh_ex (fun l => aqmh_pure_pre (fun pf => ?_)))
    (fun L M H ⟨ha,he,lA,lB,tA,tB,sAB,sBA,o⟩ => ⟨⟨lA,lB⟩,⟨tA.2.1,tA.2.2.2,tB.2.1,tB.2.2.2,sAB,sBA,(o w rfl).1,
      (o w rfl).2⟩,ha,he,tA.1,tA.2.2.1,tB.1,tB.2.2.1⟩) (fun _ _ _ h => h) (fun _ _ _ h => h)
  obtain ⟨lA,lB⟩ := l
  obtain ⟨okA,cA,okB,cB,sAB,sBA,oA,oB⟩ := pf
  dsimp only at okA cA okB cB sAB sBA oA oB ⊢
  -- record the transaction read (htab_set on the table at ts + 8)
  refine aqmh_seq (Q := fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      H0.toNat ≤ H.toNat ∧ PreTabs Ts Bs Ta Tb (fun x => x = w) H M)
    (aqmh_setCall (ofString "ts") (by decide) Ts 8 hTs _ _ Ta lA.KL lA.SD lA.C lA.N lA.KS lA.VS lA.US lA.OS lA.OPS
      lA.b H0 okA oA p0 (fun L M H h => ⟨h.2.1,h.2.2.1,h.2.2.2.1⟩) ?_ ?_) ?_
  · intro F s x H ⟨⟨A,hA⟩,_⟩ _ hx
    rcases hx with hx | hx
    · simp [EV,evalHOLExact,hA] at hx; exact ⟨A,hx.symm⟩
    · simp [EV,evalHOLExact] at hx; exact ⟨1,hx.symm⟩
  · intro L M H M' H' ⟨ha,_,mA,hA,mB,hB⟩ post
    obtain ⟨lA',tA2,tB2,sAB2,sBA2,hle,_,kO⟩ := set_sep (lX := lA) (lY := lB) ⟨mA,okA,hA,cA⟩ ⟨mB,okB,hB,cB⟩ sAB sBA post
    exact ⟨ha,hle,lA',lB,tA2,tB2,sAB2,sBA2,fun x hx => by
      subst hx; exact ⟨kO _ oA,fun c => oB (canon_mono c hle)⟩⟩
  -- w = htab_get(lds (bs + 16), addr): read-only
  refine aqmh_decCallSpec (Vn' := fun _ => False)
    (Pe := fun _ M0' H0' _ M H => M = M0' ∧ H = H0')
    (RRe := fun _ M0' H0' _ M' H' => H0'.toNat ≤ H'.toNat ∧ M' = M0')
    (Pc := fun L M H => (∃ A : BitVec 64, L.lookup (ofString "addr") = some (.val (.word A))) ∧
      H0.toNat ≤ H.toNat ∧ PreTabs Ts Bs Ta Tb (fun x => x = w) H M) (Qc := fun _ _ _ => True)
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
      preTabs_mono pt hle⟩
  -- early return of a block-written account
  refine aqmh_seq (aqmh_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩) (aqmh_return _ (fun _ _ _ _ h _ _ => h.1.2.2))
    (aqmh_conseq aqmh_skip (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ _ _ h => h))) ?_
  -- record the block pre-state read (htab_set on the table at bs + 72)
  refine aqmh_seq (Q := fun _ M H => H0.toNat ≤ H.toNat ∧ PreTabs Ts Bs Ta Tb (fun x => x = w) H M)
    (aqmh_callSpec (Vn' := fun _ => True)
      (Pe := fun _ M0' H0' _ M H => M = M0' ∧ H = H0')
      (RRe := fun _ M0' H0' _ M' H' => PreTabs Ts Bs Ta Tb (fun x => x = w) H' M' ∧ H0'.toNat ≤ H'.toNat)
      _ _ _ _ _ originalRuntimeCode_recordPreStateRead_lookup (by simp) ?_ (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
      (fun L M H v M' H' ⟨_,hle0,_⟩ ⟨pt,hle⟩ => ⟨by omega,pt⟩)) ?_
  · intro L0 M0' H0' ⟨_,hle0,lA',lB',tA',tB',sAB',sBA',o'⟩
    refine aqmh_conseq (recordPreRead_aqmh Bs hBs Tb lB'.KL lB'.SD lB'.C lB'.N lB'.KS lB'.VS lB'.US lB'.OS lB'.OPS lB'.b
      H0' tB'.2.1 (o' w rfl).2 (by omega) M0') (fun L M H ⟨e1,e2⟩ => by subst e1 e2; exact ⟨tB'.1,tB'.2.2.1,rfl,rfl⟩)
      (fun _ _ _ _ => trivial) ?_
    intro v M' H' post
    obtain ⟨lB2,tB2,tA2,sBA2,sAB2,hle,_,kO⟩ := set_sep (lX := lB') (lY := lA') tB' tA' sBA' sAB' post
    exact ⟨⟨lA',lB2,tA2,tB2,sAB2,sBA2,fun x hx => ⟨fun c => (o' x hx).1 (canon_mono c hle),kO x (o' x hx).2⟩⟩,hle⟩
  -- a = ws_get_account_optional(addr); return a
  refine aqmh_decCallSpec (Vn' := fun x => x ≠ ofString "leaf")
    (Pe := fun _ M0' H0' _ M H => M = M0' ∧ H = H0')
    (RRe := fun _ M0' H0' _ M' H' => H0'.toNat ≤ H'.toNat ∧
      ∀ x, (WsSafe SP0 FM K Pd NB x ∧ x.toNat < H0'.toNat) → M' x = M0' x)
    (Pc := fun _ M H => PreTabs Ts Bs Ta Tb (fun x => x = w) H M) (Qc := fun _ _ _ => True)
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
    exact preTabs_frame (preTabs_mono pt hle) (fun x hx => (fr x ⟨safe x hx,preTabs_below pt x hx⟩))

#print axioms preState_aqmh
#print axioms set_sep
#print axioms aqmh_rebound
#print axioms aqm_frame_of_aq
end InitECandidate.Runtime
