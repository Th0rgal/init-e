import InitECandidate.Runtime.DecodeBytesListLoop
import InitECandidate.Runtime.SszSplitVarListFirstStage
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returned facts of the length-check continuation, relative to its entry. -/
def BytesListAfterReturned {σ : Type} (t : PanSemStateFiniteExact 64 σ) (arr count maxb : BitVec 64)
    (v : ValueHOL 64) (post : PanSemStateFiniteExact 64 σ) : Prop :=
  v = .rStruct [.val (.word arr), .val (.word count)] ∧ post.memory = t.memory ∧ post.globals = t.globals ∧
    post.memaddrs = t.memaddrs ∧ ∀ k : BitVec 64, k.toNat < count.toNat → BytesListItemOK t.memaddrs t.memory arr maxb k

theorem evaluate_bytesListAfterSplit {σ : Type} (t : PanSemStateFiniteExact 64 σ) (arr count maxb : BitVec 64)
    (hr : t.locals.lookup (ofString "r") = some (.rStruct [.val (.word arr), .val (.word count)]))
    (hm : t.locals.lookup (ofString "maxb") = some (.val (.word maxb)))
    (code : t.code = originalRuntimeCode) (small : count.toNat < 2 ^ 62) (enough : 2 * count.toNat ≤ t.clock) :
    t.clock ≤ (evaluateHOLFiniteState t bytesListAfterSplit).2.clock + 2 * count.toNat ∧
      (evaluateHOLFiniteState t bytesListAfterSplit).2.clock ≤ t.clock ∧
      ((evaluateHOLFiniteState t bytesListAfterSplit).1 ≠ none ∧
        (evaluateHOLFiniteState t bytesListAfterSplit).1 ≠ some .timeOut ∧
        ∀ v, (evaluateHOLFiniteState t bytesListAfterSplit).1 = some (.returned v) →
          BytesListAfterReturned t arr count maxb v (evaluateHOLFiniteState t bytesListAfterSplit).2) := by
  obtain ⟨n1, n2⟩ := bytesList_names
  unfold bytesListAfterSplit
  apply evaluate_dec_word_post t (ofString "i") (.const 0) _ 0#64 _
    (fun r p => r ≠ none ∧ r ≠ some .timeOut ∧ ∀ v, r = some (.returned v) → BytesListAfterReturned t arr count maxb v p)
    (fun _ _ _ h => h) (by simp [evalHOLExact])
  generalize hq : setVarHOLFinite (ofString "i") (.val (.word 0#64)) t = q
  have qr : q.locals.lookup (ofString "r") = some (.rStruct [.val (.word arr), .val (.word count)]) := by
    rw [← hq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n1, hr]
  have qm : q.locals.lookup (ofString "maxb") = some (.val (.word maxb)) := by
    rw [← hq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, n2, hm]
  have qi : q.locals.lookup (ofString "i") = some (.val (.word 0#64)) := by
    rw [← hq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have qc : q.clock = t.clock := by rw [← hq]; rfl
  have qcode : q.code = originalRuntimeCode := by rw [← hq]; exact code
  have inv : BytesListInv q arr count maxb q := ⟨0#64, q.locals, rfl, qr, qm, qi, by simp, small, fun k h => by simp at h⟩
  have rank : bytesListRank q = count.toNat := by rw [bytesList_rank_eq q arr 0#64 count qi qr]; simp
  obtain ⟨result, post, run, l1, l2, nt, normal, noret⟩ := evaluate_bytesListLoop q arr count maxb qcode q inv (by omega)
  rw [rank] at l1
  rw [evaluateHOLFiniteState_seq_line780, run]
  cases result with
  | none =>
    obtain ⟨⟨i, L, shape, hr2, _, hiL, le, _, checked⟩, zero⟩ := normal rfl
    have pr : post.locals.lookup (ofString "r") = some (.rStruct [.val (.word arr), .val (.word count)]) := by
      rw [shape]; exact hr2
    have hi2 : post.locals.lookup (ofString "i") = some (.val (.word i)) := by rw [shape]; exact hiL
    rw [bytesList_rank_eq post arr i count hi2 pr] at zero
    dsimp only
    rw [evaluateHOLFiniteState_return]
    simp only [sszLocal, evalHOLExact, lookupKvarHOLExact]
    rw [pr]
    have sz : sizeOfShapeWithContextHOL post.structs
        (shapeOfHOLExact (.rStruct [.val (.word arr), .val (.word count)] : ValueHOL 64)) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    dsimp only
    rw [if_pos sz]
    have pm : post.memory = t.memory := by rw [shape, ← hq]; rfl
    have pg : post.globals = t.globals := by rw [shape, ← hq]; rfl
    have pd : post.memaddrs = t.memaddrs := by rw [shape, ← hq]; rfl
    have qm' : q.memory = t.memory := by rw [← hq]; rfl
    have qd' : q.memaddrs = t.memaddrs := by rw [← hq]; rfl
    refine ⟨by simp [emptyLocalsHOLFinite]; omega, by simp [emptyLocalsHOLFinite]; omega, by simp, by simp,
      fun v h => ?_⟩
    simp only [Option.some.injEq, PanSemResultExact.returned.injEq] at h
    subst h
    refine ⟨rfl, pm, pg, pd, fun k lt => ?_⟩
    rw [← qm', ← qd']
    exact checked k (by omega)
  | some x =>
    dsimp only
    exact ⟨by omega, by omega, by simp, nt, fun v h => absurd h (noret v)⟩

end InitECandidate.Runtime
