import InitECandidate.Runtime.StatelessCheckGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Entry at the actual At22 of the original stateless decoder, keeping the
complete prefix and middle facts. -/
def FullAt22Entry {σ : Type} (s : PanSemStateFiniteExact 64 σ) (P L H offsets : BitVec 64)
    (E : PanSemStateFiniteExact 64 σ) : Prop :=
  ∃ E8 O0 O1, StPrefixEntry s E8 P L offsets O0 O1 ∧ MidEntry E8 (P + 2) H offsets E

/-- The actual original stateless decoder At0..At21 at every clock: reaches
At22 within 17 ticks (scoped) or aborts without returning within 17 ticks. -/
theorem evaluate_stateless_at22 {σ : Type} (s : PanSemStateFiniteExact 64 σ) (P L H offsets : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (hp : s.locals.lookup (ofString "p") = some (.val (.word P)))
    (hL : s.locals.lookup (ofString "len") = some (.val (.word L)))
    (hg : s.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word H))) (pointerBound : H.toNat ≤ 33806089496) :
    Reaches s (statelessAt 0) (FullAt22Entry s P L H offsets) 17 (statelessAt 22) := by
  have first : Reaches s (statelessAt 0) (fun E8 => ∃ O0 O1, StPrefixEntry s E8 P L offsets O0 O1) 6 (statelessAt 8) := by
    rcases evaluate_stateless_prefix s P L offsets code hp hL hg with ⟨E8, O0, O1, entry, eq, c1, c2⟩ | ab
    · exact Or.inl ⟨E8, ⟨O0, O1, entry⟩, c1, c2, by rw [eq]; exact scoped_refl _⟩
    · exact Or.inr ab
  have composed := reaches_trans s _ (statelessAt 8) (statelessAt 22) _ (FullAt22Entry s P L H offsets) 6 11 first (by
    rintro E8 ⟨O0, O1, entry⟩
    obtain ⟨_, _, _, el, eg, _, ec, _⟩ := id entry
    have np : ofString "len" ≠ ofString "p" := by decide_cbv
    refine reaches_mono E8 _ _ _ _ 11 11 (le_refl _) (fun E h => ⟨E8, O0, O1, entry, h⟩)
      (evaluate_stateless_mid E8 (P + 2) H offsets (by rw [ec]; exact code)
        (by rw [el]; simp [HolFiniteMapExact.lookup_update, FUPDATE, np])
        (by rw [eg]; exact hg) (by rw [eg]; exact heap) pointerBound))
  exact composed

/-- Ordered outer and payload offsets at the actual At22 locals, in Nat. -/
def StatelessAt22Geometry {σ : Type} (L : BitVec 64) (E : PanSemStateFiniteExact 64 σ) : Prop :=
  ∃ ONP OW OPL OVH ORQ : BitVec 64,
    E.locals.lookup (ofString "o_npr") = some (.val (.word ONP)) ∧
    E.locals.lookup (ofString "o_wit") = some (.val (.word OW)) ∧
    E.locals.lookup (ofString "o_pl") = some (.val (.word OPL)) ∧
    E.locals.lookup (ofString "o_vh") = some (.val (.word OVH)) ∧
    E.locals.lookup (ofString "o_rq") = some (.val (.word ORQ)) ∧
    E.locals.lookup (ofString "nlen") = some (.val (.word (OW - ONP))) ∧
    2 ≤ L.toNat ∧ ONP = 16 ∧ 16 ≤ OW.toNat ∧ OW.toNat ≤ L.toNat - 2 ∧ (OW - ONP).toNat = OW.toNat - 16 ∧
    OPL = 44 ∧ 44 ≤ OVH.toNat ∧ OVH.toNat ≤ ORQ.toNat ∧ ORQ.toNat ≤ OW.toNat - 16

theorem fullAt22_geometry {σ : Type} (s : PanSemStateFiniteExact 64 σ) (P L H offsets : BitVec 64)
    (E : PanSemStateFiniteExact 64 σ) (h : FullAt22Entry s P L H offsets E) : StatelessAt22Geometry L E := by
  obtain ⟨E8, O0, O1, pre, mid⟩ := h
  obtain ⟨notShort, _, notShort16, _, _, _, _, _, _, _, _, mem8, check8⟩ := pre
  obtain ⟨_, _, _, _, _, _, X88, OPL, OVH, ORQ, _, _, _, memE, _, _, _, lnpr, lwit, _, _, lnlen, lpl, lvh, lrq, _, checkE⟩ := mid
  obtain ⟨g0, g1, g2⟩ := check2_geometry E8 offsets (L - 2) check8
  obtain ⟨h0, h1, h2, h3⟩ := check3_geometry E offsets _ checkE
  have L2 : (L - 2).toNat = L.toNat - 2 := by
    have := notLt_toNat _ _ notShort
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using this)]; simp
  have ne816 : offsets + 16 ≠ offsets + 8 := by rw [Ne, BitVec.add_right_inj]; decide
  have ne160 : offsets + 16 ≠ offsets := by
    intro e; have := congrArg (· - offsets) e; simp at this
  have ne80 : offsets + 8 ≠ offsets := by
    intro e; have := congrArg (· - offsets) e; simp at this
  have r0 : memWord E.memory offsets = OPL := by rw [memE]; simp [memWord, wmem, Ne.symm ne160, Ne.symm ne80]
  have r1 : memWord E.memory (offsets + 8) = OVH := by rw [memE]; simp [memWord, wmem, Ne.symm ne816]
  have r2 : memWord E.memory (offsets + 16) = ORQ := by rw [memE]; simp [memWord, wmem]
  rw [r0] at h0; rw [r1] at h1 h2; rw [r2] at h2 h3
  have sub : (memWord E8.memory (offsets + 8) - memWord E8.memory offsets).toNat =
      (memWord E8.memory (offsets + 8)).toNat - 16 := by
    rw [g0, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using g1)]; simp
  refine ⟨_, _, OPL, OVH, ORQ, lnpr, lwit, lpl, lvh, lrq, lnlen, ?_, g0, g1, by omega, sub, h0, h1, h2, by omega⟩
  have := notLt_toNat _ _ notShort; simpa using this

/-- The middle span [np, np+nlen) lies inside the original input [P, P+L). -/
theorem fullAt22_span {σ : Type} (s : PanSemStateFiniteExact 64 σ) (P L H offsets : BitVec 64)
    (E : PanSemStateFiniteExact 64 σ) (h : FullAt22Entry s P L H offsets E) (inputFits : P.toNat + L.toNat < 2 ^ 64) :
    ∃ NP NL : BitVec 64, E.locals.lookup (ofString "np") = some (.val (.word NP)) ∧
      E.locals.lookup (ofString "nlen") = some (.val (.word NL)) ∧
      NP.toNat = P.toNat + 18 ∧ NP.toNat + NL.toNat ≤ P.toNat + L.toNat := by
  obtain ⟨E8, O0, O1, pre, mid⟩ := h
  obtain ⟨notShort, _, notShort16, _, _, _, _, _, _, _, _, _, check8⟩ := pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, lnp, lnlen, _⟩ := mid
  obtain ⟨g0, g1, g2⟩ := check2_geometry E8 offsets (L - 2) check8
  have L2v := notLt_toNat _ _ notShort
  have L16 := notLt_toNat _ _ notShort16
  have L2 : (L - 2).toNat = L.toNat - 2 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simpa using L2v)]; simp
  simp only [L2] at L16 g2
  simp at L2v L16
  rw [g0] at lnp lnlen
  generalize hW : memWord E8.memory (offsets + 8) = W at g1 g2 lnlen
  have g1' : (16 : BitVec 64) ≤ W := by rw [BitVec.le_def]; simpa using g1
  refine ⟨_, _, lnp, lnlen, ?_, ?_⟩
  · rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  · rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_sub_of_le g1']
    simp; omega

#print axioms evaluate_stateless_at22
#print axioms fullAt22_geometry
#print axioms fullAt22_span
end InitECandidate.Runtime
