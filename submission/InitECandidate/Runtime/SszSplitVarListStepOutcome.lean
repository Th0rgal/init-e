import InitECandidate.Runtime.SszSplitVarListStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Current-pointer store and the two local updates after the checks. -/
theorem sszSplitStep_rest_in {σ : Type} (c : PanSemStateFiniteExact 64 σ) (m1 : BitVec 64 → HolWordLab 64)
    (p o arr i prev : BitVec 64)
    (hp : c.locals.lookup (ofString "p") = some (.val (.word p)))
    (ho : c.locals.lookup (ofString "o") = some (.val (.word o)))
    (ha : c.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (hi : c.locals.lookup (ofString "i") = some (.val (.word i)))
    (hprev : c.locals.lookup (ofString "prev") = some (.val (.word prev)))
    (dom : c.memaddrs (arr + i * 16)) :
    evaluateHOLFiniteState ({c with memory := m1} : PanSemStateFiniteExact 64 σ)
      (.seq sszSplitStoreCur (.seq (.assign .local (ofString "prev") (sszLocal "o"))
        (.assign .local (ofString "i") (.op .add [sszLocal "i", .const 1])))) =
      (none, setVarHOLFinite (ofString "i") (.val (.word (i + 1)))
        (setVarHOLFinite (ofString "prev") (.val (.word o)) {c with memory := wmem m1 (arr + i * 16) (p + o)})) := by
  obtain ⟨_, _, _, _, _, _, _, n8, _, _, _, _, n13, _, _, _, _, _⟩ := sszsplit_names
  let c1 : PanSemStateFiniteExact 64 σ := {c with memory := m1}
  rw [evaluateHOLFiniteState_seq_line780]
  unfold sszSplitStoreCur
  rw [sszStore_in c1 (arr + i * 16) (p + o) _ _ (sszSplit_curAddr c1 arr i ha hi)
    (sszSplit_sum c1 p o "p" "o" hp ho) dom]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,
    sszSplit_assign_prev ({c1 with memory := wmem c1.memory (arr + i * 16) (p + o)} : PanSemStateFiniteExact 64 σ)
      o prev ho hprev]
  dsimp only
  rw [sszSplit_assign_i _ i (by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm n13, c1, hi])]

theorem sszSplitStep_rest_out {σ : Type} (c : PanSemStateFiniteExact 64 σ) (m1 : BitVec 64 → HolWordLab 64)
    (p o arr i prev : BitVec 64)
    (hp : c.locals.lookup (ofString "p") = some (.val (.word p)))
    (ho : c.locals.lookup (ofString "o") = some (.val (.word o)))
    (ha : c.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (hi : c.locals.lookup (ofString "i") = some (.val (.word i)))
    (hprev : c.locals.lookup (ofString "prev") = some (.val (.word prev)))
    (dom : ¬ c.memaddrs (arr + i * 16)) :
    evaluateHOLFiniteState ({c with memory := m1} : PanSemStateFiniteExact 64 σ)
      (.seq sszSplitStoreCur (.seq (.assign .local (ofString "prev") (sszLocal "o"))
        (.assign .local (ofString "i") (.op .add [sszLocal "i", .const 1])))) = (some .error, {c with memory := m1}) := by
  let c1 : PanSemStateFiniteExact 64 σ := {c with memory := m1}
  rw [evaluateHOLFiniteState_seq_line780]
  unfold sszSplitStoreCur
  rw [sszStore_out c1 (arr + i * 16) (p + o) _ _ (sszSplit_curAddr c1 arr i ha hi)
    (sszSplit_sum c1 p o "p" "o" hp ho) dom]

#print axioms sszSplitStep_rest_in
end InitECandidate.Runtime
