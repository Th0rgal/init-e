import InitECandidate.Runtime.SszSplitVarListLoopB
import InitECandidate.Runtime.SszSplitVarListAfterAlloc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def sszSliceEnd (off : BitVec 64 → BitVec 64) (len count k : BitVec 64) : BitVec 64 :=
  if k.toNat + 1 < count.toNat then off (k + 1) else len

/-- Returned slice array: for every k < count, cell arr+16k holds p+o_k and
cell arr+16k+8 holds end_k-o_k with first ≤ o_k ≤ end_k ≤ len (end_k is the
next offset, or len for the last slice); all other words are unchanged. -/
def SszSplitSlices (m0 : SszMem) (dom : BitVec 64 → Prop) (p len first arr count : BitVec 64) (M : SszMem) : Prop :=
  ∃ off : BitVec 64 → BitVec 64,
    (∀ k : BitVec 64, k.toNat < count.toNat →
      ¬ off k < first ∧ ¬ sszSliceEnd off len count k < off k ∧ ¬ len < sszSliceEnd off len count k ∧
      dom (arr + k * 16) ∧ M (arr + k * 16) = .word (p + off k) ∧
      dom (arr + k * 16 + 8) ∧ M (arr + k * 16 + 8) = .word (sszSliceEnd off len count k - off k)) ∧
    (∀ a, (∀ k : BitVec 64, k.toNat < count.toNat → a ≠ arr + k * 16 ∧ a ≠ arr + k * 16 + 8) → M a = m0 a)

theorem sszSplit_return {σ : Type} (u : PanSemStateFiniteExact 64 σ) (arr count : BitVec 64)
    (ha : u.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (hc : u.locals.lookup (ofString "count") = some (.val (.word count))) :
    evaluateHOLFiniteState u (.return (.rstruct [sszLocal "arr", sszLocal "count"])) =
      (some (.returned (.rStruct [.val (.word arr), .val (.word count)])), emptyLocalsHOLFinite u) := by
  simp [sszLocal, evalHOLExact, evalListHOLExact, ha, hc, shapeOfHOLExact]

theorem evaluate_sszSplitTailB {σ : Type} (t : PanSemStateFiniteExact 64 σ) (m0 : SszMem) (dom : BitVec 64 → Prop)
    (p len first count arr prev : BitVec 64) (off : BitVec 64 → BitVec 64)
    (look : SszSplitLocals t.locals p len first count arr count prev)
    (cells : SszSplitCellsOK m0 dom p len first arr off count t.memory) (tdom : t.memaddrs = dom)
    (nz : count ≠ 0) (small : count.toNat < 2 ^ 60) (hprev : prev = off (count - 1)) :
    ∀ v, (evaluateHOLFiniteState t sszSplitTail).1 = some (.returned v) →
      SszSplitSlices m0 dom p len first arr count (evaluateHOLFiniteState t sszSplitTail).2.memory := by
  obtain ⟨hp, hlen, hfirst, hcount, harr, hi, hpr⟩ := look
  obtain ⟨c0, c8, frame⟩ := cells
  have pos : 0 < count.toNat := Nat.pos_of_ne_zero (fun z => nz (BitVec.eq_of_toNat_eq (by simp [z])))
  have predNat : (count - 1).toNat = count.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  intro v returned
  unfold sszSplitTail at returned ⊢
  rw [evaluateHOLFiniteState_seq_line780] at returned ⊢
  by_cases dt : t.memaddrs (arr + (count - 1) * 16 + 8)
  · rw [sszStore_in t _ _ _ _ (sszSplit_tailAddr t arr count harr hcount)
      (sszSplit_diff t len prev "len" "prev" hlen hpr) dt] at returned ⊢
    dsimp only at returned ⊢
    rw [sszSplit_return ({t with memory := wmem t.memory (arr + (count - 1) * 16 + 8) (len - prev)} :
      PanSemStateFiniteExact 64 σ) arr count harr hcount] at returned ⊢
    change SszSplitSlices m0 dom p len first arr count (wmem t.memory (arr + (count - 1) * 16 + 8) (len - prev))
    refine ⟨off, ?_, ?_⟩
    · intro k hk
      obtain ⟨a0, b0, d0, m0'⟩ := c0 k hk
      have ne0 : arr + k * 16 ≠ arr + (count - 1) * 16 + 8 :=
        fun h => sszCell_len_ne_ptr arr (count - 1) k (by omega) (by omega) h.symm
      refine ⟨a0, ?_, ?_, d0, by simp only [wmem, if_neg ne0]; exact m0', ?_⟩
      · unfold sszSliceEnd; split
        · rename_i h; exact (c8 k h).1
        · exact b0
      · unfold sszSliceEnd; split
        · rename_i h
          have k1 : (k + 1).toNat = k.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
          exact (c0 (k + 1) (by omega)).2.1
        · exact BitVec.lt_irrefl len
      · unfold sszSliceEnd
        split
        · rename_i h
          obtain ⟨_, d8, m8⟩ := c8 k h
          have kne : k ≠ count - 1 := fun e => by have := congrArg BitVec.toNat e; omega
          have ne8 : arr + k * 16 + 8 ≠ arr + (count - 1) * 16 + 8 :=
            sszCell_len_ne arr k (count - 1) (by omega) (by omega) kne
          exact ⟨d8, by simp only [wmem, if_neg ne8]; exact m8⟩
        · rename_i h
          have keq : k = count - 1 := BitVec.eq_of_toNat_eq (by omega)
          subst keq
          rw [← tdom]
          refine ⟨dt, ?_⟩
          simp only [wmem, if_true]
          rw [hprev]
    · intro a ex
      have k0 : (count - 1).toNat < count.toNat := by omega
      have e := (ex (count - 1) k0).2
      simp only [wmem, if_neg e]
      exact frame a (fun k hk => ex k hk)
  · rw [sszStore_out t _ _ _ _ (sszSplit_tailAddr t arr count harr hcount)
      (sszSplit_diff t len prev "len" "prev" hlen hpr) dt] at returned
    simp at returned

#print axioms evaluate_sszSplitTailB
end InitECandidate.Runtime
