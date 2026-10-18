import InitECandidate.Runtime.SszSplitVarListSlices
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_dec_word_R {σ : Type} (s : PanSemStateFiniteExact 64 σ) (name : MlS) (e : ExpHOL 64)
    (body : ProgHOL 64) (w : BitVec 64)
    (R : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 σ → Prop)
    (stable : ∀ r t L, R r t → R r {t with locals := L})
    (he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some (.val (.word w)))
    (h : R (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body).1
        (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body).2) :
    R (evaluateHOLFiniteState s (.dec name .one e body)).1 (evaluateHOLFiniteState s (.dec name .one e body)).2 := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  simp only [he, shapeOfHOLExact, shapeEqHOL, if_true]
  exact stable _ _ _ h

theorem evaluate_sszSplitInnerB {σ : Type} (q : PanSemStateFiniteExact 64 σ) (p len first count arr : BitVec 64)
    (look : SszSplitLocals q.locals p len first count arr 0 first)
    (code : q.code = originalRuntimeCode) (nz : count ≠ 0) (small : count.toNat < 2 ^ 60)
    (enough : 2 * count.toNat ≤ q.clock) :
    ∀ v, (evaluateHOLFiniteState q (.seq sszSplitLoop sszSplitTail)).1 = some (.returned v) →
      SszSplitSlices q.memory q.memaddrs p len first arr count
        (evaluateHOLFiniteState q (.seq sszSplitLoop sszSplitTail)).2.memory := by
  have inv : SszSplitInvB q p len first count arr q :=
    ⟨0#64, first, q.locals, q.memory, fun _ => first, rfl, look, by simp, small, fun _ => rfl,
      fun h => absurd rfl h, sszSplitCells_initial _ _ _ _ _ _ _⟩
  have rank : sszSplitRank q = count.toNat := by
    rw [sszSplit_rank_eq q 0#64 count look.2.2.2.2.2.1 look.2.2.2.1]; simp
  obtain ⟨result, post, run, _, _, _, normal, noret⟩ :=
    evaluate_sszSplitLoopB q p len first count arr code q inv (by omega)
  intro v returned
  rw [evaluateHOLFiniteState_seq_line780, run] at returned ⊢
  cases result with
  | none =>
    obtain ⟨⟨i, prev, L, M, off, shape, look2, le, _, _, prevOff, cells⟩, zero⟩ := normal rfl
    have postLocals : post.locals = L := by rw [shape]
    have pi : post.locals.lookup (ofString "i") = some (.val (.word i)) := by rw [postLocals]; exact look2.2.2.2.2.2.1
    have pn : post.locals.lookup (ofString "count") = some (.val (.word count)) := by
      rw [postLocals]; exact look2.2.2.2.1
    rw [sszSplit_rank_eq post i count pi pn] at zero
    have ieq : i = count := BitVec.eq_of_toNat_eq (by omega)
    subst ieq
    have pm : post.memory = M := by rw [shape]
    have pd : post.memaddrs = q.memaddrs := by rw [shape]
    dsimp only at returned ⊢
    exact evaluate_sszSplitTailB post q.memory q.memaddrs p len first i arr prev off
      (by rw [postLocals]; exact look2) (by rw [pm]; exact cells) pd nz small (prevOff nz) v returned
  | some x =>
    dsimp only at returned
    exact absurd returned (noret v)

theorem evaluate_sszSplitAfterAllocB {σ : Type} (r : PanSemStateFiniteExact 64 σ) (p len first count arr : BitVec 64)
    (hp : r.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : r.locals.lookup (ofString "len") = some (.val (.word len)))
    (hfirst : r.locals.lookup (ofString "first") = some (.val (.word first)))
    (hcount : r.locals.lookup (ofString "count") = some (.val (.word count)))
    (harr : r.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (code : r.code = originalRuntimeCode) (nz : count ≠ 0) (small : count.toNat < 2 ^ 60)
    (enough : 2 * count.toNat ≤ r.clock) :
    ∀ v, (evaluateHOLFiniteState r sszSplitAfterAlloc).1 = some (.returned v) →
      SszSplitSlices r.memory r.memaddrs p len first arr count (evaluateHOLFiniteState r sszSplitAfterAlloc).2.memory := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18⟩ := sszsplit_names
  unfold sszSplitAfterAlloc
  let R : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 σ → Prop := fun res t =>
    ∀ v, res = some (.returned v) → SszSplitSlices r.memory r.memaddrs p len first arr count t.memory
  apply evaluate_dec_word_R r (ofString "i") (.const 0) _ 0#64 R (fun _ _ _ h => h) (by simp [evalHOLExact])
  let q1 := setVarHOLFinite (ofString "i") (.val (.word 0#64)) r
  have q1first : q1.locals.lookup (ofString "first") = some (.val (.word first)) := by
    simp [q1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n10, hfirst]
  apply evaluate_dec_word_R q1 (ofString "prev") (sszLocal "first") _ first R (fun _ _ _ h => h)
    (by simp [sszLocal, evalHOLExact, q1first])
  exact evaluate_sszSplitInnerB (setVarHOLFinite (ofString "prev") (.val (.word first)) q1) p len first count arr
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [q1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n8, n9, n10, n11, n12, n13, n14, n15, n16,
        n17, n18, Ne.symm n8, Ne.symm n9, Ne.symm n10, Ne.symm n11, Ne.symm n12, Ne.symm n13, Ne.symm n14,
        Ne.symm n15, Ne.symm n16, Ne.symm n17, Ne.symm n18, hp, hlen, hfirst, hcount, harr])
    code nz small enough

#print axioms evaluate_sszSplitAfterAllocB
end InitECandidate.Runtime
