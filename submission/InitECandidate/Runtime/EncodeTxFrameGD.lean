import InitECandidate.Runtime.EncGenericGD
import InitECandidate.Runtime.CheckTransactionUGD
/-!
Frame contract of the actual `encode_transaction` from an explicit domain fence: `Fence D DF`, `DF + 8 ≤ 2^62`,
heap cap `≤ DF`, watched word below `P0`. Every store lands at or above the entry heap pointer, so the registry
(`regT_below`) and outside words (`regT_out_lt`) are kept.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section rb
variable {D : BitVec 64 → Prop} {B : Bool}

/-- The registry with content at heap pointer `H` depends only on memory below `H`. -/
theorem regT_below {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M M' : Mem}
    {ko : Fin n} (h : RegT n c T Out H M D B ko) (keep : ∀ x, x.toNat < H.toNat → M' x = M x) :
    RegT n c T Out H M' D B ko := by
  obtain ⟨l,pure,mem,tc,ab⟩ := h
  have fitT : ∀ i, (T i).toNat + 72 < 2 ^ 64 := fun i => by have := (pure.1 i).1.eEnd; omega
  refine ⟨l,pure,regMem_frame mem fitT (fun x ⟨i,hx⟩ => keep x ?_),tc.frame (pure.1 ko).1.cnt.le (fun x hx => keep x ?_),ab⟩
  · rcases hx with rfl | ⟨_,hi⟩
    · by_contra hc
      exact (pure.1 i).2 (Or.inr (Or.inr (by omega)))
    · have := (pure.1 i).1.hdrP; omega
  · rcases hx with ⟨_,hi⟩ | h | h | h | h | h
    · have := (pure.1 ko).1.hdrP; omega
    · exact ab x (Or.inl h)
    · exact ab x (Or.inr (Or.inl h))
    · exact ab x (Or.inr (Or.inr (Or.inl h)))
    · exact ab x (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact ab x (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- Outside words lie below the heap pointer. -/
theorem regT_out_lt {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {H : BitVec 64} {M : Mem}
    {ko : Fin n} (h : RegT n c T Out H M D B ko) {x : BitVec 64} (hx : Out x) : x.toNat < H.toNat := by
  obtain ⟨_,pure,_,_,_⟩ := h
  by_contra hc
  exact pure.2.2 x hx ko (Or.inr (Or.inr (by omega)))

#print axioms regT_below
end rb

section et
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {DF : Nat} {SP0 P0 FM J C SKB Nj : BitVec 64} {G0 : GA}

/-- The actual `encode_transaction(tx)` (tail call `tx_encode_generic(tx, 0, 0)`): every store at or above the entry
heap pointer `H0`, the heap pointer stays at or above `H0`. -/
theorem encodeTx_win (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF) (H0 : BitVec 64)
    (hw : w.toNat < H0.toNat) :
    AQGD D B (JWSN SP0 P0 FM G0 J C SKB Nj) w (fun _ => False) (fun _ _ G => HeapIs G H0) (fun _ _ _ => False)
      (fun _ _ G => HGe H0 G) (sourceFunctionBody Guest.guestFn_encode_transaction) := by
  have e : sourceFunctionBody Guest.guestFn_encode_transaction =
      .call none (ofString "tx_encode_generic") [.var .local (ofString "tx"),.const 0#64,.const 0#64] := by
    unfold sourceFunctionBody
    rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    simp only [Guest.guestFn_encode_transaction,InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,List.map_cons,List.map_nil,
      Option.map_some,Option.map_none]
  rw [e]
  exact aqgd_tailCallSpecS (Vn' := fun _ => False)
    (Pe := fun _ _ _ L _ G => (∃ c : BitVec 64, L.lookup (ofString "chain_id") = some (.val (.word c))) ∧ HeapIs G H0)
    (RRe := fun _ _ _ _ _ G => HGe H0 G) _ _ _ _ _ originalRuntimeCode_txEncodeGeneric_lookup
    (fun _ _ _ _ _ h => h.elim)
    (fun _ _ _ _ => aqgd_conseq (encGeneric_win hF hDF hcap H0 hw) (fun _ _ _ h => h) (fun _ _ _ _ => trivial)
      (fun _ _ _ h => h))
    (fun s values callee rs _ H hG hH _ args lookup => by
      unfold GIs at hG; subst hG
      rw [evalListHOLFinite_eq_toExact] at args
      cases hv : s.locals.lookup (ofString "tx") with
      | none => simp [evalListHOLExact,evalHOLExact,hv] at args
      | some vv =>
      simp [evalListHOLExact,evalHOLExact,hv] at args
      subst args
      have e := callee_eq originalRuntimeCode_txEncodeGeneric_lookup lookup
      exact ⟨⟨0#64,by rw [e]; simp (config := {decide := true})⟩,hH⟩)
    (fun _ _ _ _ _ _ _ h => h)

#print axioms encodeTx_win
end et

section fc
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {DF : Nat} {SP0 P0 FM J C SKB U : BitVec 64} {G0 : GA}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {Excl : BitVec 64 → Prop}

/-- Frame contract of the actual `encode_transaction` under the explicit domain fence: all its stores land at or
above the entry heap pointer, so memory below it (outside words, the registry) is kept. -/
theorem encodeTx_frameC (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (hw : w.toNat < P0.toNat) :
    FrameC SP0 P0 FM G0 J C SKB w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_encode_transaction) := by
  intro H0 Nj M0 F s code dom aw sl H hH ⟨reg,hM,hHe,hn⟩
  unfold GIs at hH; subst hH
  obtain ⟨hP0,_,_⟩ := jws_heap_facts aw hHe
  have win := fun (x : BitVec 64) (hx : x.toNat < H0.toNat) =>
    encodeTx_win (w := x) (B := B) (Nj := Nj) hF hDF hcap H0 hx F s code dom ⟨aw,hn⟩ (fun _ h => h.elim) _ rfl hHe
  obtain ⟨m,a,nn,r,cc,bb⟩ := win w (by omega)
  refine ⟨m,fun cont => (a cont).1,fun e => (nn e).2.elim (fun _ h => h.2.elim),fun v e => ?_,cc,bb⟩
  obtain ⟨H',hH',H1,hH1,le⟩ := r v e
  unfold GIs at hH'; subst hH'
  have keep : ∀ x, x.toNat < H0.toNat → (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_encode_transaction)).2.memory x = s.memory x :=
    fun x hx => (win x hx).1
  subst hM
  refine ⟨_,rfl,H1,hH1,le,regT_mono (regT_below reg keep) le,
    (a (Or.inr (Or.inr (Or.inr ⟨_,e⟩)))).2,fun x hx _ => keep x (regT_out_lt reg hx)⟩

#print axioms encodeTx_frameC

theorem encodeTx_frameCU (hF : Fence D DF) (hDF : DF + 8 ≤ 2 ^ 62) (hcap : 33806089496 ≤ DF)
    (hw : w.toNat < P0.toNat) :
    FrameCU SP0 P0 FM G0 J C SKB U w n c T Out ko D B Excl (sourceFunctionBody Guest.guestFn_encode_transaction) :=
  frameCU_of_frameC (encodeTx_frameC hF hDF hcap hw)
    (keepsWs_of_installed originalRuntimeCode_encodeTransaction_lookup (by decide))

#print axioms encodeTx_frameCU
end fc
end InitECandidate.Runtime
