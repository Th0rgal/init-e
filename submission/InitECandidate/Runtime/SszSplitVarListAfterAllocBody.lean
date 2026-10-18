import InitECandidate.Runtime.SszSplitVarListAfterAlloc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_sszSplitAfterAlloc {σ : Type} (r : PanSemStateFiniteExact 64 σ) (p len first count arr : BitVec 64)
    (hp : r.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : r.locals.lookup (ofString "len") = some (.val (.word len)))
    (hfirst : r.locals.lookup (ofString "first") = some (.val (.word first)))
    (hcount : r.locals.lookup (ofString "count") = some (.val (.word count)))
    (harr : r.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (code : r.code = originalRuntimeCode) (small : count.toNat < 2 ^ 62) (enough : 2 * count.toNat ≤ r.clock) :
    r.clock ≤ (evaluateHOLFiniteState r sszSplitAfterAlloc).2.clock + 2 * count.toNat ∧
      (evaluateHOLFiniteState r sszSplitAfterAlloc).2.clock ≤ r.clock ∧
      SszSplitAfterQ arr count (evaluateHOLFiniteState r sszSplitAfterAlloc).1 ∧
      (∀ v, (evaluateHOLFiniteState r sszSplitAfterAlloc).1 = some (.returned v) →
        (evaluateHOLFiniteState r sszSplitAfterAlloc).2.globals = r.globals) := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18⟩ := sszsplit_names
  unfold sszSplitAfterAlloc
  apply evaluate_dec_word_transfer r (ofString "i") (.const 0) _ 0#64 _ _ (by simp [evalHOLExact])
  let q1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) r
  have q1first : q1.locals.lookup (ofString "first") = some (.val (.word first)) := by
    simp [q1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n10, hfirst]
  apply evaluate_dec_word_transfer q1 (ofString "prev") (sszLocal "first") _ first _ _
    (by simp [sszLocal, evalHOLExact, q1first])
  exact evaluate_sszSplitInner (setVarHOLFinite (ofString "prev") (.val (.word first)) q1) p len first count arr
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [q1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n8, n9, n10, n11, n12, n13, n14, n15, n16,
        n17, n18, Ne.symm n8, Ne.symm n9, Ne.symm n10, Ne.symm n11, Ne.symm n12, Ne.symm n13, Ne.symm n14,
        Ne.symm n15, Ne.symm n16, Ne.symm n17, Ne.symm n18, hp, hlen, hfirst, hcount, harr])
    code small enough

#print axioms evaluate_sszSplitAfterAlloc
end InitECandidate.Runtime
