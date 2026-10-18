import InitECandidate.Runtime.DecodeBytesListStep
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Slice k's length cell is readable and at most maxb. -/
def BytesListItemOK (dom : BitVec 64 → Prop) (m : SszMem) (arr maxb k : BitVec 64) : Prop :=
  dom (arr + k * 16#64 + 8#64) ∧ ¬ maxb < memWord m (arr + k * 16#64 + 8#64)

def BytesListInv {σ : Type} (base : PanSemStateFiniteExact 64 σ) (arr count maxb : BitVec 64)
    (s : PanSemStateFiniteExact 64 σ) : Prop :=
  ∃ i : BitVec 64, ∃ L, s = {base with locals := L, clock := s.clock} ∧
    L.lookup (ofString "r") = some (.rStruct [.val (.word arr), .val (.word count)]) ∧
    L.lookup (ofString "maxb") = some (.val (.word maxb)) ∧ L.lookup (ofString "i") = some (.val (.word i)) ∧
    i.toNat ≤ count.toNat ∧ count.toNat < 2 ^ 62 ∧
    ∀ k : BitVec 64, k.toNat < i.toNat → BytesListItemOK base.memaddrs base.memory arr maxb k

def bytesListRank {σ : Type} (s : PanSemStateFiniteExact 64 σ) : Nat :=
  match s.locals.lookup (ofString "i"), s.locals.lookup (ofString "r") with
  | some (.val (.word i)), some (.rStruct [_, .val (.word n)]) => n.toNat - i.toNat
  | _, _ => 0

theorem bytesList_rank_eq {σ : Type} (s : PanSemStateFiniteExact 64 σ) (arr i n : BitVec 64)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (hr : s.locals.lookup (ofString "r") = some (.rStruct [.val (.word arr), .val (.word n)])) :
    bytesListRank s = n.toNat - i.toNat := by
  simp [bytesListRank, hi, hr]

theorem bytesList_names : ofString "i" ≠ ofString "r" ∧ ofString "i" ≠ ofString "maxb" := by
  constructor <;> decide_cbv

theorem evaluate_bytesListLoop {σ : Type} (base : PanSemStateFiniteExact 64 σ) (arr count maxb : BitVec 64)
    (code : base.code = originalRuntimeCode)
    (s : PanSemStateFiniteExact 64 σ) (inv : BytesListInv base arr count maxb s)
    (ticks : bytesListRank s * 2 ≤ s.clock) :
    ∃ result post, evaluateHOLFiniteState s bytesListLoop = (result, post) ∧
      s.clock ≤ post.clock + bytesListRank s * 2 ∧ post.clock ≤ s.clock ∧ result ≠ some .timeOut ∧
      (result = none → BytesListInv base arr count maxb post ∧ bytesListRank post = 0) ∧
      (∀ value, result ≠ some (.returned value)) := by
  obtain ⟨n1, n2⟩ := bytesList_names
  have guard : ∀ state, BytesListInv base arr count maxb state →
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .less (sszLocal "i") (.rfield 1 (sszLocal "r"))) =
        some (.val (.word (if bytesListRank state = 0 then 0 else 1))) := by
    rintro state ⟨i, L, shape, hr, _, hi, le, small, _⟩
    have si : state.locals.lookup (ofString "i") = some (.val (.word i)) := by rw [shape]; exact hi
    have sr : state.locals.lookup (ofString "r") = some (.rStruct [.val (.word arr), .val (.word count)]) := by
      rw [shape]; exact hr
    rw [bytesList_rank_eq state arr i count si sr]
    by_cases zero : count.toNat - i.toNat = 0
    · simp [sszLocal, evalHOLFinite, evalHOLExact, si, sr, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, zero]
      rw [if_pos (by omega)]; omega
    · simp [sszLocal, evalHOLFinite, evalHOLExact, si, sr, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, zero]
      rw [if_pos (by omega)]; omega
  have entry : ∀ state, BytesListInv base arr count maxb state →
      BytesListInv base arr count maxb (decClockHOLFinite state) := by
    rintro state ⟨i, L, shape, rest⟩
    exact ⟨i, L, by rw [shape]; rfl, rest⟩
  have entryRank : ∀ state : PanSemStateFiniteExact 64 σ, bytesListRank (decClockHOLFinite state) = bytesListRank state := by
    intro state; rfl
  have step : ∀ state, BytesListInv base arr count maxb state → 0 < bytesListRank state → 1 ≤ state.clock →
      ∃ post, state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧
        ((evaluateHOLFiniteState state bytesListStep = (none,post) ∧ BytesListInv base arr count maxb post ∧
            bytesListRank post < bytesListRank state) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ value, result ≠ .returned value) ∧
           evaluateHOLFiniteState state bytesListStep = (some result,post))) := by
    rintro state ⟨i, L, shape, hr, hm, hi, le, small, checked⟩ positive clock
    have look : ∀ k, state.locals.lookup k = L.lookup k := by intro k; rw [shape]
    have si := (look _).trans hi
    have sr := (look _).trans hr
    rw [bytesList_rank_eq state arr i count si sr] at positive
    have stateCode : state.code = originalRuntimeCode := by rw [shape]; exact code
    obtain ⟨c1, c2, outcome⟩ := bytesListStep_outcome state arr count i maxb sr si ((look _).trans hm) stateCode
      (by omega)
    cases run : evaluateHOLFiniteState state bytesListStep with
    | mk result post =>
      rw [run] at c1 c2 outcome
      dsimp only at c1 c2 outcome
      refine ⟨post, c1, c2, ?_⟩
      rcases outcome with ⟨none_, postEq, dom, ok⟩ | ⟨x, hx, ab⟩
      · subst none_
        have succ : (i + 1).toNat = i.toNat + 1 := by rw [BitVec.toNat_add]; simp; omega
        have pl : ∀ k, k ≠ ofString "i" → post.locals.lookup k = L.lookup k := by
          intro k hk; rw [postEq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk, look]
        have pi : post.locals.lookup (ofString "i") = some (.val (.word (i + 1))) := by
          rw [postEq]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        refine Or.inl ⟨rfl, ⟨i + 1, post.locals, ?_, (pl _ (Ne.symm n1)).trans hr, (pl _ (Ne.symm n2)).trans hm, pi,
          by omega, small, ?_⟩, ?_⟩
        · rw [postEq, shape]; rfl
        · intro k lt
          rw [succ] at lt
          by_cases eq : k.toNat = i.toNat
          · have : k = i := BitVec.eq_of_toNat_eq eq
            subst this
            rw [shape] at dom ok
            exact ⟨dom, ok⟩
          · exact checked k (by omega)
        · rw [bytesList_rank_eq post arr (i + 1) count pi ((pl _ (Ne.symm n1)).trans hr),
            bytesList_rank_eq state arr i count si sr, succ]
          omega
      · subst hx
        exact Or.inr ⟨x, ab.1, ab.2.1, ab.2.2.1, ab.2.2.2, rfl⟩
  have result := evaluate_ranked_loop_exits_invariant _ bytesListStep (BytesListInv base arr count maxb)
    bytesListRank 1 guard entry entryRank step s inv (by simpa using ticks)
  simpa [bytesListLoop] using result

#print axioms evaluate_bytesListLoop
end InitECandidate.Runtime
