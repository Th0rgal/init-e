import InitECandidate.Runtime.GetCodeGD
import InitECandidate.Runtime.BalanceWriterGD
import InitECandidate.Runtime.RegistryCarry
import InitECandidate.Runtime.BoGlobalKeep
import InitECandidate.Runtime.OriginalTxPrefixCode
import InitECandidate.Runtime.OriginalMinCode
import InitECandidate.Runtime.StateInitJournalSource
/-!
Concrete `process_transaction` prefix over the content-carrying registry: callee wrappers keeping `PXR` (read-only
callees with any parameter shapes, frame-contract callees, `alloc`, `get_account`, `bo`-array stores, global
assignment) and their composition from `bal_index = index + 1` to the `increment_nonce` call site.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- A declared call to a memory-and-globals-keeping function, preserving a caller invariant stable under the new
local. -/
theorem aqgd_decCall_mf {I I' Q Q2 : GA → Mem → GA → Prop} (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (mf : MemoryFrame body) (nb : noTopBreak body = true)
    (nc : noTopContinue body = true)
    (hup : ∀ L M G v, I L M G → I' (L.update (name,v)) M G)
    (hcont : AQGD D B A w (fun _ => False) I' Q RR cont)
    (hres : ∀ L M G L' M' G', I L M G → Q L' M' G' → Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B A w (fun _ => False) I Q2 RR (.decCall name shape function arguments cont) :=
  aqgd_decCallSpec (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    (Pc := I') (Qc := Q) _ _ _ _ _ _ _ installed allOne (fun _ M0' G0' _ => aqgd_of_mf mf nb nc M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim)
    (fun L M G v M' G' pre ⟨e1,e2⟩ _ => by rw [e1,e2]; exact hup L M G v pre) hcont hres

/-- A result-assigning call to a memory-and-globals-keeping function. -/
theorem aqgd_callAssign_mf {I Q : GA → Mem → GA → Prop} (name function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one) (mf : MemoryFrame body) (nb : noTopBreak body = true)
    (nc : noTopContinue body = true) (hup : ∀ L M G v, I L M G → Q (L.update (name,v)) M G) :
    AQGD D B A w (fun _ => False) I Q RR (.call (some (some (.local,name),none)) function arguments) :=
  aqgd_callAssignF (Vn' := fun _ => False)
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    _ _ _ _ _ _ installed allOne (fun h => h) (fun _ M0' G0' _ => aqgd_of_mf mf nb nc M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩)
    (fun L M G v M' G' pre ⟨e1,e2⟩ => by rw [e1,e2]; exact hup L M G v pre)

/-- `aqgd_decCallSpec` for a callee spec over no scalar locals: no parameter-shape side condition. -/
theorem aqgd_decCallSpecF {P Pc Qc Q : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop}
    (Pe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (RRe : HolFiniteMapExact MlS (ValueHOL 64) → Mem → HolFiniteMapExact MlS (ValueHOL 64) → ValueHOL 64 → Mem → HolFiniteMapExact MlS (ValueHOL 64) → Prop)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (hb : ∀ L0 M0 H0, P L0 M0 H0 → AQGD D B A w (fun _ => False) (Pe L0 M0 H0) (fun _ _ _ => True) (RRe L0 M0 H0) body)
    (hpe : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) values callee rs, A s.globals →
      ∀ H, GIs s.globals H → P s.locals s.memory H → SL Vn s.locals →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
      Pe s.locals s.memory H callee s.memory H)
    (hshape : Vn name → shape = .one)
    (hret : ∀ L M H v M' H', P L M H → RRe L M H v M' H' → shapeEqHOL (shapeOfHOLExact v) shape = true →
      Pc (L.update (name,v)) M' H')
    (hc : AQGD D B A w Vn Pc Qc RR cont)
    (hq : ∀ L M H L' M' H', P L M H → Qc L' M' H' → Q (L'.resVarEq (name,L.lookup name)) M' H') :
    AQGD D B A w Vn P Q RR (.decCall name shape function arguments cont) := by
  intro F state code dom aw sl H hH pre
  rw [evaluateHOLFiniteState_decCall_total]
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
      split
      · exact aqgd_of_nc rfl (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
      · have frame := hb _ _ _ pre F (callEntryStateHOLFinite state callee) code dom aw
          (fun _ h => h.elim) H (by exact hH) (hpe state values callee foundShape aw H hH pre sl args lookup')
        have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) found
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) found with
        | mk rb bodyPost =>
          rw [bodyRun] at frame meta'
          obtain ⟨m1,a1,_,r1,_,_⟩ := frame
          change bodyPost.memory w = state.memory w at m1
          dsimp only [fixClockHOLFinite]
          cases rb with
          | none => exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · rename_i ok
                simp only [Bool.and_eq_true] at ok
                have cslx : SL Vn (state.locals.update (name,v)) :=
                  sl_update sl name v (fun hn => by rw [hshape hn] at ok; exact scalar_of_shape' ok.1)
                obtain ⟨H',hH',rr⟩ := r1 v rfl
                have pc := hret _ _ _ _ _ _ pre rr ok.1
                obtain ⟨m2,a2,n2,r2,c2,b2⟩ := hc F (setVarHOLFinite name v { bodyPost with clock := _, locals := state.locals })
                  (by exact meta'.1.trans code) (by obtain ⟨d1,d2,d3⟩ := dom; exact ⟨fun a ha => d1 a (meta'.2.1 ▸ ha),meta'.2.1.trans d2,meta'.2.2.1.trans d3⟩)
                  (by exact a1 (Or.inr (Or.inr (Or.inr ⟨_,rfl⟩)))) cslx H' (by exact hH') pc
                refine ⟨m2.trans m1,a2,fun e => ?_,r2,c2,b2⟩
                obtain ⟨sl2,H2,hH2,q2⟩ := n2 e
                exact ⟨sl_restore sl2 sl name,H2,hH2,hq _ _ _ _ _ _ pre q2⟩
              · exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)
            | _ => exact aqgd_of_nc m1 (fun h => by rcases h with h | h | h | ⟨_,h⟩ <;> cases h)

/-- A declared call to a memory-and-globals-keeping function with any parameter shapes. -/
theorem aqgd_decCall_mfF {I I' Q Q2 : GA → Mem → GA → Prop} (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (hup : ∀ L M G v, I L M G → I' (L.update (name,v)) M G)
    (hcont : AQGD D B A w (fun _ => False) I' Q RR cont)
    (hres : ∀ L M G L' M' G', I L M G → Q L' M' G' → Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B A w (fun _ => False) I Q2 RR (.decCall name shape function arguments cont) :=
  aqgd_decCallSpecF
    (Pe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : GA) (M : Mem) (G : GA) => M = M0' ∧ G = G0')
    (RRe := fun (_ : GA) (M0' : Mem) (G0' : GA) (_ : ValueHOL 64) (M' : Mem) (G' : GA) => M' = M0' ∧ G' = G0')
    (Pc := I') (Qc := Q) _ _ _ _ _ _ _ installed (fun _ M0' G0' _ => aqgd_of_mf mf nb nc M0' G0')
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl,rfl⟩) (fun h => h.elim)
    (fun L M G v M' G' pre ⟨e1,e2⟩ _ => by rw [e1,e2]; exact hup L M G v pre) hcont hres

#print axioms aqgd_decCall_mfF

#print axioms aqgd_decCall_mf
#print axioms aqgd_callAssign_mf
variable {SP0 P0 FM : BitVec 64} {G0 : GA}

/-- The journal/key-buffer arena with the block-output record pointer `bo = Bo`. -/
def JWSB (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB Bo : BitVec 64) (g : GA) : Prop :=
  JWS SP0 P0 FM G0 J C SKB g ∧ g.lookup (ofString "bo") = some (.val (.word Bo))

theorem aqgd_jwsb {J C SKB Bo : BitVec 64} {Vn : MlS → Prop} {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64}
    (h : AQGD D B (JWS SP0 P0 FM G0 J C SKB) w Vn P Q RR p) (hk : keepsG (ofString "bo") goodBo p = true) :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w Vn P Q RR p :=
  aqgd_strengthen (X := fun g => g.lookup (ofString "bo") = some (.val (.word Bo))) h
    (fun s code x => (evaluate_keeps_bo p hk s code).trans x)

/-- Updating a global outside the arena, journal, key-buffer and `bo` names keeps `JWSB`. -/
theorem jwsb_update {J C SKB Bo : BitVec 64} {g : GA} (h : JWSB SP0 P0 FM G0 J C SKB Bo g) (name : MlS)
    (hn : name ∉ [ofString "frame_mem_ptr",ofString "scratch_ptr",ofString "heap_ptr",ofString "journal",
      ofString "journal_cap",ofString "sk_buf",ofString "bo"]) (hs : name ∉ staticGlobalNames) (v : ValueHOL 64) :
    JWSB SP0 P0 FM G0 J C SKB Bo (g.update (name,v)) := by
  obtain ⟨⟨⟨⟨hf,⟨sp,hsp,a1,a2⟩,⟨hp,hhp,b1,b2,b3⟩,st⟩,hj,hc⟩,hk⟩,hb⟩ := h
  have ne : ∀ m : MlS, m ≠ name → (g.update (name,v)).lookup m = g.lookup m :=
    fun m hm => by simp [HolFiniteMapExact.lookup_update,FUPDATE,hm,Ne.symm hm]
  have n1 : ofString "frame_mem_ptr" ≠ name := fun e => hn (by rw [← e]; simp)
  have n2 : ofString "scratch_ptr" ≠ name := fun e => hn (by rw [← e]; simp)
  have n3 : ofString "heap_ptr" ≠ name := fun e => hn (by rw [← e]; simp)
  have n4 : ofString "journal" ≠ name := fun e => hn (by rw [← e]; simp)
  have n5 : ofString "journal_cap" ≠ name := fun e => hn (by rw [← e]; simp)
  have n6 : ofString "sk_buf" ≠ name := fun e => hn (by rw [← e]; simp)
  have n7 : ofString "bo" ≠ name := fun e => hn (by rw [← e]; simp)
  refine ⟨⟨⟨⟨by rw [ne _ n1]; exact hf,⟨sp,by rw [ne _ n2]; exact hsp,a1,a2⟩,⟨hp,by rw [ne _ n3]; exact hhp,b1,b2,b3⟩,
    fun m hm => ?_⟩,by rw [ne _ n4]; exact hj,by rw [ne _ n5]; exact hc⟩,by rw [ne _ n6]; exact hk⟩,
    by rw [ne _ n7]; exact hb⟩
  have : m ≠ name := fun e => hs (e ▸ hm)
  rw [ne m this]; exact st m hm

#print axioms jwsb_update

/-- Registry-and-frame part of the `process_transaction` prefix state: heap pointer not below the entry heap, the
content-carrying registry at it, some journal counter, and every outside word outside the exception region `Excl`
equal to the entry memory. -/
def PXR (n : Nat) (c T : Fin n → BitVec 64) (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool)
    (Excl : BitVec 64 → Prop) (H0 : BitVec 64) (M0 : Mem) (M : Mem) (G : GA) : Prop :=
  ∃ H Nj : BitVec 64, HeapIs G H ∧ H0.toNat ≤ H.toNat ∧ RegT n c T Out H M D B ko ∧
    G.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ Excl x → M x = M0 x

/-- Frame contract of a callee (a temporary scoped hypothesis where no proof exists yet): from the registry at any
heap pointer and counter, every return keeps the registry at the exit heap, the counter, and every outside word
outside `Excl`. -/
def FrameC (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB : BitVec 64) (w : BitVec 64) (n : Nat) (c T : Fin n → BitVec 64)
    (Out : BitVec 64 → Prop) (ko : Fin n) (D : BitVec 64 → Prop) (B : Bool) (Excl : BitVec 64 → Prop)
    (body : ProgHOL 64) : Prop :=
  ∀ (H0 Nj : BitVec 64) (M0 : Mem),
    AQGD D B (JWS SP0 P0 FM G0 J C SKB) w (fun _ => True)
      (fun _ M G => RegT n c T Out H0 M D B ko ∧ M = M0 ∧ HeapIs G H0 ∧
        G.lookup (ofString "journal_n") = some (.val (.word Nj)))
      (fun _ _ _ => True)
      (fun _ M' G' => ∃ H', HeapIs G' H' ∧ H0.toNat ≤ H'.toNat ∧ RegT n c T Out H' M' D B ko ∧
        G'.lookup (ofString "journal_n") = some (.val (.word Nj)) ∧ ∀ x, Out x → ¬ Excl x → M' x = M0 x)
      body
theorem heapIs_unique {G : GA} {H H' : BitVec 64} (h : HeapIs G H) (h' : HeapIs G H') : H = H' := by
  unfold HeapIs at h h'; rw [h] at h'; simpa using h'

section fc
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {Excl : BitVec 64 → Prop}
  {J C SKB Bo H0 : BitVec 64} {M0 : Mem}

/-- A declared call to a callee with a frame contract, preserving `PXR` and a locals predicate stable under the new
local. -/
theorem aqgd_decCall_fc {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (fc : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl body) (hk : keepsG (ofString "bo") goodBo body = true)
    (hup : ∀ L v, LP L → shapeEqHOL (shapeOfHOLExact v) shape = true → LP' (L.update (name,v)))
    (hcont : AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LP' L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q RR cont)
    (hres : ∀ L M G L' M' G', LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
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
    refine aqgd_conseq (aqgd_jwsb (fc H1 Nj M0') hk) ?_ (fun _ _ _ _ => trivial) ?_
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
theorem aqgd_call_fc {LP : GA → Prop} (function : MlS) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (allOne : ∀ p ∈ parameters, p.2 = .one)
    (fc : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl body) (hk : keepsG (ofString "bo") goodBo body = true) :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
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
    refine aqgd_conseq (aqgd_jwsb (fc H1 Nj M0') hk) ?_ (fun _ _ _ _ => trivial) ?_
    · intro L M G ⟨hM,hG⟩
      subst hM hG
      exact ⟨reg,rfl,hH,hn⟩
    · intro v M' G' post
      exact ⟨H1,Nj,hH,hn,post⟩
  · intro L M G v M' G' ⟨lp,H1,Nj,hH,hle,_,_,fr⟩ ⟨H1',Nj',hH',_,H',hH2,hle',reg',hn',fr'⟩
    have e := heapIs_unique hH hH'
    subst e
    exact ⟨lp,H',Nj',hH2,le_trans hle hle',reg',hn',fun x ho hx => (fr' x ho hx).trans (fr x ho hx)⟩

#print axioms aqgd_decCall_fc
#print axioms aqgd_call_fc
end fc
section wr
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {Excl : BitVec 64 → Prop}
  {J C SKB Bo H0 : BitVec 64} {M0 : Mem}

/-- A word-valued declared allocation: the heap grows, memory is unchanged, `PXR` is kept. -/
theorem aqgd_decCall_alloc {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name : MlS) (sz : BitVec 64)
    {cont : ProgHOL 64}
    (hup : ∀ L (y : BitVec 64), LP L → LP' (L.update (name,.val (.word y))))
    (hcont : AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LP' L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q RR cont)
    (hres : ∀ L M G L' M' G', LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
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
    refine aqgd_conseq (aqgd_jwsb (aqgd_jws (aqgd_of_aqg (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_allocation_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (alloc_aqmh (SP0 := SP0) (P0 := P0) (FM := FM) (G0 := G0) (w := w) sz H1 M0')))
      (keepsSkBuf_of_installed originalRuntimeCode_allocation_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_allocation_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
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

#print axioms aqgd_decCall_alloc

set_option maxHeartbeats 4000000 in
/-- A global assignment to a name outside the arena, journal, key-buffer, `bo` and heap/counter names keeps `PXR`. -/
theorem aqgd_assignGlobal_other {LP : GA → Prop} (name : MlS) (e : ExpHOL 64)
    (hn : name ∉ [ofString "frame_mem_ptr",ofString "scratch_ptr",ofString "heap_ptr",ofString "journal",
      ofString "journal_cap",ofString "sk_buf",ofString "bo",ofString "journal_n"]) (hs : name ∉ staticGlobalNames) :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
      (fun L M G => LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G) RR (.assign .global name e) := by
  refine aqgd_assignGlobal _ _ (fun s v aw ⟨lp,H1,Nj,hH,hle,reg,hn',fr⟩ _ _ => ?_)
  have h1 : ofString "heap_ptr" ≠ name := fun h => hn (by rw [← h]; simp)
  have h2 : ofString "journal_n" ≠ name := fun h => hn (by rw [← h]; simp)
  refine ⟨jwsb_update aw name (fun m => hn (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at m ⊢
    rcases m with h | h | h | h | h | h | h <;> simp [h])) hs v,lp,H1,Nj,?_,hle,reg,?_,fr⟩
  · unfold HeapIs at hH ⊢
    simp only [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    rw [if_neg (by simpa [beq_iff_eq] using (Ne.symm h1))]; exact hH
  · simp only [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    rw [if_neg (by simpa [beq_iff_eq] using (Ne.symm h2))]; exact hn'

#print axioms aqgd_assignGlobal_other
end wr
section wr2
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {Excl : BitVec 64 → Prop}
  {J C SKB Bo H0 : BitVec 64} {M0 : Mem}

/-- A word store into an exception-region outside word (not a pointer cell) keeps `PXR`. -/
theorem aqgd_store_excl {LP : GA → Prop} (d v : ExpHOL 64) (a : BitVec 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), JWSB SP0 P0 FM G0 J C SKB Bo s.globals → DomD D B s →
      LP s.locals → PXR n c T Out ko D B Excl H0 M0 s.memory s.globals → EV s d = some (.val (.word a)))
    (hv : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) x, LP s.locals → EV s v = some x →
      ∃ y : BitVec 64, x = .val (.word y))
    (hwa : w ≠ a) (hOutA : Out a ∧ ∀ i, a ≠ c i) (hExA : Excl a) :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
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

#print axioms aqgd_store_excl
end wr2
section ga
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo H0 Ts Bs : BitVec 64} {M0 : Mem}

set_option maxHeartbeats 16000000 in
/-- A declared `get_account(x)` call (account read tables `kA`, `kB`) keeping `PXR`: the registry with the content
of `ko` and every outside word (all outside words are off the workspace and below `P0`). -/
theorem aqgd_decCall_getAccount {LP LP' : GA → Prop} {Q Q2 : GA → Mem → GA → Prop} (name xname : MlS)
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
    (hcont : AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LP' L ∧ PXR n c T Out ko D B Excl H0 M0 M G) Q RR cont)
    (hres : ∀ L M G L' M' G', LP L ∧ PXR n c T Out ko D B Excl H0 M0 M G → Q L' M' G' →
      Q2 (L'.resVarEq (name,L.lookup name)) M' G') :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
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
    refine aqgd_conseq (aqgd_jwsb (aqgd_jws (aqgd_of_aqg (aqg_withA (aqg_of_aqmh_j (J := J) (C := C) (N := Nj)
      originalRuntimeCode_account_lookup (by decide_cbv) (by decide_cbv) (by decide_cbv)
      (accountRegT_aqmh n c T kA kB ko hAB hAo hBo Ts Bs hTs hBs hcA hcB Out hOut H1 p1 K Pd NB hK0 hPd0 hNB0
        safe (hOutSafe w hOut).1 hwP l pure M0' mem ab))))
      (keepsSkBuf_of_installed originalRuntimeCode_account_lookup (by decide)))
      (keepsBo_of_installed originalRuntimeCode_account_lookup (by decide))) ?_ (fun _ _ _ _ => trivial) ?_
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

#print axioms aqgd_decCall_getAccount
end ga
/-- Locals of the `process_transaction` prefix: the `index` argument. -/
def LPI (Ix : BitVec 64) (L : GA) : Prop := L.lookup (ofString "index") = some (.val (.word Ix))

/-- `LPI` with the `enc` pair returned by `encode_transaction`. -/
def LPE (Ix : BitVec 64) (L : GA) : Prop :=
  LPI Ix L ∧ ∃ a b : BitVec 64, L.lookup (ofString "enc") = some (.rStruct [.val (.word a),.val (.word b)])

/-- `LPI` with the one-word `sender` pointer. -/
def LPS (Ix : BitVec 64) (L : GA) : Prop :=
  LPI Ix L ∧ ∃ S : BitVec 64, L.lookup (ofString "sender") = some (.val (.word S))

theorem lpi_upd {Ix : BitVec 64} {L : GA} (h : LPI Ix L) (name : MlS) (v : ValueHOL 64)
    (ne : name ≠ ofString "index") : LPI Ix (L.update (name,v)) := by
  unfold LPI at *; simp [HolFiniteMapExact.lookup_update,FUPDATE,h]; intro e; exact absurd e ne

theorem lps_upd {Ix : BitVec 64} {L : GA} (h : LPS Ix L) (name : MlS) (v : ValueHOL 64)
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender") : LPS Ix (L.update (name,v)) := by
  obtain ⟨h1,S,h2⟩ := h
  exact ⟨lpi_upd h1 name v ne,S,by simp [HolFiniteMapExact.lookup_update,FUPDATE,h2]; intro e; exact absurd e ne'⟩

theorem resVarEq_lookup_ne' {β : Type} (m : HolFiniteMapExact MlS β) (key k : MlS) (opt : Option β)
    (ne : k ≠ key) : (HolFiniteMapExact.resVarEq m (key, opt)).lookup k = m.lookup k := by
  cases opt with
  | none => simp [FDOMSUB_HOL, ne]
  | some v => simp [FUPDATE_HOL, ne]

theorem lps_res {Ix : BitVec 64} {L : GA} (h : LPS Ix L) (name : MlS) (o : Option (ValueHOL 64))
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender") : LPS Ix (L.resVarEq (name,o)) := by
  obtain ⟨h1,S,h2⟩ := h
  exact ⟨by unfold LPI at *; rw [resVarEq_lookup_ne' _ _ _ _ (Ne.symm ne)]; exact h1,S,
    by rw [resVarEq_lookup_ne' _ _ _ _ (Ne.symm ne')]; exact h2⟩

section pxh
variable {X : Mem → GA → Prop} {QM : Mem → GA → Prop} {Ix : BitVec 64} {A : GA → Prop}

/-- A declaration of a local other than `index`/`sender`, keeping `LPS` and a memory/globals invariant. -/
theorem aqgd_dec_lps (name : MlS) (shape : ShapeHOL) (init : ExpHOL 64) {body : ProgHOL 64}
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender")
    (hb : AQGD D B A w (fun _ => False) (fun L M G => LPS Ix L ∧ X M G) (fun _ M G => QM M G) RR body) :
    AQGD D B A w (fun _ => False) (fun L M G => LPS Ix L ∧ X M G) (fun _ M G => QM M G) RR
      (.dec name shape init body) :=
  aqgd_dec _ _ _ (fun h => h.elim) (fun _ v _ _ _ pre _ _ _ => ⟨lps_upd pre.1 _ v ne ne',pre.2⟩) hb
    (fun _ _ _ _ _ _ _ h => h)

/-- A declared call to a memory-and-globals-keeping function (any parameter shapes), keeping `LPS`. -/
theorem aqgd_decCall_lps (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender")
    (hb : AQGD D B A w (fun _ => False) (fun L M G => LPS Ix L ∧ X M G) (fun _ M G => QM M G) RR cont) :
    AQGD D B A w (fun _ => False) (fun L M G => LPS Ix L ∧ X M G) (fun _ M G => QM M G) RR
      (.decCall name shape function arguments cont) :=
  aqgd_decCall_mfF _ _ _ _ _ _ _ installed mf nb nc (fun _ _ _ v pre => ⟨lps_upd pre.1 _ v ne ne',pre.2⟩) hb
    (fun _ _ _ _ _ _ _ h => h)

/-- The same with an `LPS`-restoring (locals-dependent) postcondition, for calls nested inside a branch. -/
theorem aqgd_decCall_lpsR (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) {cont : ProgHOL 64}
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (mf : MemoryFrame body) (nb : noTopBreak body = true) (nc : noTopContinue body = true)
    (ne : name ≠ ofString "index") (ne' : name ≠ ofString "sender")
    (hb : AQGD D B A w (fun _ => False) (fun L M G => LPS Ix L ∧ X M G) (fun L M G => LPS Ix L ∧ X M G) RR cont) :
    AQGD D B A w (fun _ => False) (fun L M G => LPS Ix L ∧ X M G) (fun L M G => LPS Ix L ∧ X M G) RR
      (.decCall name shape function arguments cont) :=
  aqgd_decCall_mfF _ _ _ _ _ _ _ installed mf nb nc (fun _ _ _ v pre => ⟨lps_upd pre.1 _ v ne ne',pre.2⟩) hb
    (fun _ _ _ _ _ _ _ h => ⟨lps_res h.1 _ _ ne ne',h.2⟩)

end pxh

section px
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko kA kB : Fin n}
  {Excl : BitVec 64 → Prop} {J C SKB Bo H0 Ts Bs : BitVec 64} {M0 : Mem}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- The actual `process_transaction` body from `bal_index = index + 1` (just after `state_fresh_tx()`) to the
`increment_nonce(sender)` call: from the content-carrying registry `PXR` and the `index` word, every path either
leaves early (raise/error, frames kept by each step) or reaches the `increment_nonce` site with `PXR`, `index` and a
one-word `sender`. Real specs: `bal_index` assignment, the two block-output transaction-array stores (into `Excl`),
`alloc`, `get_account` (registry with `ko` content), and the read-only callees `tx_chain_id`,
`validate_transaction`, `calculate_total_blob_gas`, `fee_mul`, `min` (whole-program memory/globals decisions).
Temporary scoped frame contracts (remaining obligations): `encode_transaction`, `recover_sender_with_chain_id`,
`check_transaction`, `calculate_blob_gas_price`. -/
theorem processTx_prefix_aqgd {QM : Mem → GA → Prop} (Ix Arr : BitVec 64)
    -- temporary scoped callee frame contracts (named obligations)
    (fcEnc : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_encode_transaction))
    (fcRec : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl
      (sourceFunctionBody Guest.guestFn_recover_sender_with_chain_id))
    (fcChk : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_check_transaction))
    (fcBgp : FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl
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
    (hrest : AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
      (fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G) (fun _ M G => QM M G) RR
      (stateInitSpineDrop 28 (sourceFunctionBody Guest.guestFn_process_transaction))) :
    AQGD D B (JWSB SP0 P0 FM G0 J C SKB Bo) w (fun _ => False)
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
  refine aqgd_seq (aqgd_assignGlobal_other _ _ (by decide) (by decide)) ?_
  -- enc = encode_transaction(tx)
  refine aqgd_decCall_fc (LP' := LPE Ix) _ _ _ _ _ _ _ originalRuntimeCode_encodeTransaction_lookup (by simp) fcEnc
    (keepsBo_of_installed originalRuntimeCode_encodeTransaction_lookup (by decide))
    (fun L v lp ok => ⟨lpi_upd lp _ v (by decide),by
      obtain ⟨a,b,rfl⟩ := pair_of_shape ok
      exact ⟨a,b,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩⟩) ?_ (fun _ _ _ _ _ _ _ h => h)
  -- the two block-output transaction-array stores
  have arr : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), JWSB SP0 P0 FM G0 J C SKB Bo s.globals → DomD D B s →
      PXR n c T Out ko D B Excl H0 M0 s.memory s.globals →
      s.globals.lookup (ofString "bo") = some (.val (.word Bo)) ∧ s.memaddrs (Bo + 24) ∧ s.memory (Bo + 24) = .word Arr :=
    fun s aw dom ⟨_,_,_,_,_,_,fr⟩ => ⟨aw.2,dom.2.1 ▸ hBoD,(fr _ hBoO hBoE).trans hArr⟩
  refine aqgd_seq (aqgd_store_excl _ _ _ (fun s aw dom lp px => ?_) (fun s x lp ev => ?_) hw0 hO0 hE0) ?_
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
  refine aqgd_seq (aqgd_store_excl _ _ _ (fun s aw dom lp px => ?_) (fun s x lp ev => ?_) hw8 hO8 hE8) ?_
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
  refine aqgd_decCall_alloc (LP' := LPS Ix) _ _
    (fun L y lp => ⟨lpi_upd lp _ _ (by decide),y,by simp [HolFiniteMapExact.lookup_update,FUPDATE]⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  -- recover_sender_with_chain_id(tx, chain id, sender)
  refine aqgd_seq (aqgd_call_fc _ _ _ _ _ originalRuntimeCode_recoverSender_lookup (by simp) fcRec
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
  refine aqgd_decCall_fc (LP' := LPS Ix) _ _ _ _ _ _ _ originalRuntimeCode_checkTransaction_lookup (by simp) fcChk
    (keepsBo_of_installed originalRuntimeCode_checkTransaction_lookup (by decide))
    (fun L v lp _ => lps_upd lp _ v (by decide) (by decide)) ?_ (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq aqgd_skip ?_
  -- tx_blob_gas_used = calculate_total_blob_gas(tx)
  refine aqgd_decCall_lps _ _ _ _ _ _ _ originalRuntimeCode_totalBlobGas_lookup
    (memoryFrame_of_good originalRuntimeCode_totalBlobGas_lookup (by decide) (by decide))
    (by body_check Guest.guestFn_calculate_total_blob_gas) (by body_check Guest.guestFn_calculate_total_blob_gas)
    (by decide) (by decide) ?_
  -- acct = get_account(sender)
  refine aqgd_decCall_getAccount (LP' := LPS Ix) _ _ hAB hAo hBo hTs hBs hcA hcB hOut hwP p0 K Pd NB hK0 hPd0 hNB0
    safe hOutSafe hkoWs (fun _ lp => lp.2) (fun L y lp => lps_upd lp _ _ (by decide) (by decide)) ?_
    (fun _ _ _ _ _ _ _ h => h)
  refine aqgd_seq aqgd_skip ?_
  refine aqgd_dec_lps _ _ _ (by decide) (by decide) ?_
  -- blob gas fee branch
  refine aqgd_seq (aqgd_ite (CT := fun _ _ _ => True) (CF := fun _ _ _ => True) _
    (fun _ _ _ _ _ _ _ _ => ⟨fun _ => trivial,fun _ => trivial⟩)
    (aqgd_conseq (aqgd_decCall_fc (LP' := LPS Ix) (Q := fun L M G => LPS Ix L ∧ PXR n c T Out ko D B Excl H0 M0 M G)
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
#print axioms processTx_prefix_aqgd
end px
end InitECandidate.Runtime
