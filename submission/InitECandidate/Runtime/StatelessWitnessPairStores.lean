import InitECandidate.Runtime.StatelessWitnessReturned
import InitECandidate.Runtime.StatelessHashRequestWitnessReturned
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def witnessPairStores (name : MlS) (first second : BitVec 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [.var .local (ofString "si"),.const first]) (.rfield 0 (.var .local name)))
    (.seq (.store (.op .add [.var .local (ofString "si"),.const second]) (.rfield 1 (.var .local name))) rest)

theorem source_witness_pair_stores :
    statelessAt 40 = witnessPairStores (ofString "st0") 40 48 (statelessAt 42) ∧
    statelessAt 43 = witnessPairStores (ofString "cd") 56 64 (statelessAt 45) ∧
    statelessAt 46 = witnessPairStores (ofString "hd") 72 80 (statelessAt 48) := by
  rw [source_stateless_witness_store40,source_stateless_witness_store41,
    source_stateless_witness_store43,source_stateless_witness_store44,
    source_stateless_witness_store46,source_stateless_witness_store47]
  exact ⟨rfl,rfl,rfl⟩

/-- The actual two field stores expose the real updated memory and both
readable header cells. Every memory word except those two is retained. -/
theorem witness_pair_stores_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (name : MlS) (first second si array count : BitVec 64) (rest : ProgHOL 64) (v : ValueHOL 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (atPair : s.locals.lookup name = some (.rStruct [.val (.word array),.val (.word count)]))
    (different : first ≠ second)
    (run : evaluateHOLFiniteState s (witnessPairStores name first second rest) = (some (.returned v),post)) :
    ∃ next : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState next rest = (some (.returned v),post) ∧
      next.locals = s.locals ∧ next.globals = s.globals ∧ next.memaddrs = s.memaddrs ∧ next.code = s.code ∧
      next.memaddrs (si + first) ∧ next.memaddrs (si + second) ∧
      next.memory (si + first) = .word array ∧ next.memory (si + second) = .word count ∧
      (∀ w : BitVec 64, w ≠ si + first → w ≠ si + second → next.memory w = s.memory w) := by
  unfold witnessPairStores at run
  obtain ⟨domainFirst,tail⟩ := seqStore_returned_exact s post _ _ _ (si + first) array v
    (by simp [evalHOLExact,evalListHOLExact,atSi,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,atPair]) run
  let middle : PanSemStateFiniteExact 64 F := {s with memory := wmem s.memory (si + first) array}
  obtain ⟨domainSecond,tail2⟩ := seqStore_returned_exact middle post _ _ _ (si + second) count v
    (by simp [middle,evalHOLExact,evalListHOLExact,atSi,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [middle,evalHOLExact,atPair]) tail
  refine ⟨{middle with memory := wmem middle.memory (si + second) count},tail2,rfl,rfl,rfl,rfl,domainFirst,domainSecond,?_,?_,?_⟩
  · have ne : si + first ≠ si + second := fun e => different (add_left_cancel e)
    simp [middle,wmem,ne]
  · simp [wmem]
  · intro w h1 h2
    simp [middle,wmem,h1,h2]

/-- Witness header stores below a nonempty array preserve its slice contract;
the empty-array case needs no address ordering. -/
theorem RlpSliceInputPrefix.after_pair_stores {F : Type} (s next : PanSemStateFiniteExact 64 F)
    (array count input inputLength first second : BitVec 64)
    (valid : RlpSliceInputPrefix s array input inputLength count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (domain : next.memaddrs = s.memaddrs)
    (before : count = 0 ∨ (first.toNat < array.toNat ∧ second.toNat < array.toNat))
    (frame : ∀ w : BitVec 64, w ≠ first → w ≠ second → next.memory w = s.memory w) :
    RlpSliceInputPrefix next array input inputLength count.toNat := by
  rcases before with empty | ⟨b1,b2⟩
  · subst count; exact rlpSliceInputPrefix_empty next array input inputLength
  · apply valid.after_memory_above s next array count input inputLength fits domain
    intro w above
    exact frame w (fun e => by subst w; omega) (fun e => by subst w; omega)

#print axioms source_witness_pair_stores
#print axioms witness_pair_stores_returned
#print axioms RlpSliceInputPrefix.after_pair_stores
end InitECandidate.Runtime
