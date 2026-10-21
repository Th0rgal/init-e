import InitECandidate.Runtime.WordIselCost
import Flapjack.Compiler.Backend.WordInst.Proofs.InstSelect
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Frame
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-! Instruction-selection cost transfer over the transformed code table.

The source program runs over the source code table and pays `preIselPrice`
(expression statements at their selected-code cost, `wordOptimizerLocalPrice`
elsewhere). The selected program runs over the target code table, whose every
function body is selected at its own fresh temporary (`IselCode`), and pays
`wordOptimizerLocalPrice`. Callee runs are supplied by `IselCalleeIH`, guarded
lexicographically below the body's starting termination depth and clock, so a
global clock induction can discharge it. This module states the relation and
proves the leaf case. -/

/-- The target code table is the source table with every function body
instruction-selected at its own fresh temporary. -/
def IselCode (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (src tgt : Spt (Nat × WordLangProgHOL (BitVec 64))) : Prop :=
  ∀ dest, (sptLookup dest src = none ↔ sptLookup dest tgt = none) ∧
    ∀ arity body, sptLookup dest src = some (arity, body) →
      ∃ tempF, everyVarHOL (fun x => decide (x < tempF)) body = true ∧
        sptLookup dest tgt = some (arity, WordInst.instSelectExecutable c tempF body)

/-- Related states: locals agree below the temporary, code tables are related
by `IselCode`, every other field is equal. -/
def IselRel {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (s t : WordSemStateFiniteExact 64 C F) : Prop :=
  wordLocalsRel temp s.locals t.locals ∧ IselCode c s.code t.code ∧
    t = { s with locals := t.locals, code := t.code }

/-- Final states: locals as in `inst_select_thm`, code related, other fields equal. -/
def IselPost {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (res : Option (WordSemResult 64)) (s t : WordSemStateFiniteExact 64 C F) : Prop :=
  WordSemStateFiniteExact.LrPost temp res s.locals t.locals ∧ IselCode c s.code t.code ∧
    t = { s with locals := t.locals, code := t.code }

/-- Pre-selection price: expression statements pay their selected code. -/
noncomputable def preIselPrice {C F : Type} (p : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) : Nat :=
  match p with
  | .assign _ e => selExpCost e
  | .set _ e => selExpCost e + 12
  | .store e _ => selExpCost e + 24
  | .shareInst _ _ e => selExpCost e + 13
  | p => wordOptimizerLocalPrice p s

/-- Callee runs strictly below `(td, ck)` (lexicographic in termination depth
and clock) transfer, with their runs and costs. -/
def IselCalleeIH {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (td ck : Nat) : Prop :=
  ∀ (dest arity tempF : Nat) (body : WordLangProgHOL (BitVec 64)) (s t : WordSemStateFiniteExact 64 C F)
    (res : Option (WordSemResult 64)) (rst : WordSemStateFiniteExact 64 C F),
    sptLookup dest s.code = some (arity, body) →
    everyVarHOL (fun x => decide (x < tempF)) body = true →
    sptLookup dest t.code = some (arity, WordInst.instSelectExecutable c tempF body) →
    Prod.Lex (· < ·) (· < ·) (s.termdep, s.clock) (td, ck) →
    IselRel c tempF s t → evaluate body s = (res, rst) → res ≠ some .error →
    ∃ rstT, evaluate (WordInst.instSelectExecutable c tempF body) t = (res, rstT) ∧
      IselPost c tempF res rst rstT ∧
      wordExecutionCost wordOptimizerLocalPrice (WordInst.instSelectExecutable c tempF body) t ≤
        wordExecutionCost preIselPrice body s

/-- The pre-selection price dominates the optimizer price on every node. -/
theorem optimizer_le_preIsel {C F : Type} (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice p s ≤ preIselPrice p s := by
  cases p <;> simp only [preIselPrice, Nat.le_refl]
  all_goals simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget]

/-- The optimizer price does not read the state. -/
theorem optimizerPrice_state {C F : Type} (p : WordLangProgHOL (BitVec 64))
    (s t : WordSemStateFiniteExact 64 C F) : wordOptimizerLocalPrice p s = wordOptimizerLocalPrice p t := by
  cases p <;> rfl

open Flapjack.Compiler.Backend.WordToWord in
/-- A leaf run keeps the code table, compile function and oracle. -/
theorem leaf_frame_const {C F : Type} (p : WordLangProgHOL (BitVec 64)) (hp : cscLeaf p = true)
    (s : WordSemStateFiniteExact 64 C F) :
    (evaluate p s).2.code = s.code ∧ (evaluate p s).2.compileOracle = s.compileOracle ∧
      (evaluate p s).2.compile = s.compile := by
  have h := evaluate_tgt_frame s.code s.compileOracle s.compile s (fun _ => rfl) p hp
  have e : tgtState s.code s.compileOracle s.compile s = s := rfl
  rw [e] at h
  have h2 := congrArg Prod.snd h
  refine ⟨?_, ?_, ?_⟩ <;> rw [h2] <;> rfl

theorem lrPost_of_match {res : Option (WordSemResult 64)} {temp : Nat} {l l' : Spt (WordLocW 64)}
    (h : match res with
      | none => wordLocalsRel temp l l'
      | some (.break _) => wordLocalsRel temp l l'
      | some (.continue _) => wordLocalsRel temp l l'
      | some _ => l = l') : WordSemStateFiniteExact.LrPost temp res l l' := by
  rcases res with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> exact h

theorem cscLeaf_isLeaf {p : WordLangProgHOL (BitVec 64)} (hp : Compiler.Backend.WordToWord.cscLeaf p = true) :
    isLeafProg p = true := by
  cases p <;> simp_all [Compiler.Backend.WordToWord.cscLeaf, isLeafProg]

theorem iselCode_mem {c : Compiler.Encoders.Asm.AsmConfigExact 64} {src tgt : Spt (Nat × WordLangProgHOL (BitVec 64))}
    (h : IselCode c src tgt) (n : Nat) : sptMem n tgt = sptMem n src := by
  have hn := (h n).1
  apply propext
  rw [sptMem_iff_lookup, sptMem_iff_lookup]
  constructor
  · rintro ⟨v, hv⟩
    cases hs : sptLookup n src with
    | none => rw [hn.1 hs] at hv; cases hv
    | some w => exact ⟨w, rfl⟩
  · rintro ⟨v, hv⟩
    cases ht : sptLookup n tgt with
    | none => rw [hn.2 ht] at hv; cases hv
    | some w => exact ⟨w, rfl⟩

open Flapjack.Compiler.Backend.WordToWord in
/-- A leaf that selection leaves unchanged transfers: same result, related
final state, and its optimizer price is at most its pre-selection price. -/
theorem isel_leaf_transfer {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (p : WordLangProgHOL (BitVec 64)) (hp : cscLeaf p = true) (s t : WordSemStateFiniteExact 64 C F)
    (res : Option (WordSemResult 64)) (rst : WordSemStateFiniteExact 64 C F)
    (vars : everyVarHOL (fun x => decide (x < temp)) p = true) (rel : IselRel c temp s t)
    (run : evaluate p s = (res, rst)) (ok : res ≠ some .error) :
    ∃ rstT, evaluate p t = (res, rstT) ∧ IselPost c temp res rst rstT ∧
      wordExecutionCost wordOptimizerLocalPrice p t ≤ wordExecutionCost preIselPrice p s := by
  obtain ⟨hl, hcode, ht⟩ := rel
  obtain ⟨loc', h1, h2⟩ := WordSemStateFiniteExact.locals_rel_evaluate_thm p s res rst t.locals temp
    ⟨run, ok, vars, hl⟩
  have tEq : tgtState t.code s.compileOracle s.compile { s with locals := t.locals } = t :=
    (rfl : tgtState t.code s.compileOracle s.compile { s with locals := t.locals } =
      { s with locals := t.locals, code := t.code }).trans ht.symm
  have frame := evaluate_tgt_frame t.code s.compileOracle s.compile { s with locals := t.locals }
    (fun n => iselCode_mem hcode n) p hp
  rw [tEq, h1] at frame
  obtain ⟨cEq, oEq, ccEq⟩ := leaf_frame_const p hp s
  rw [run] at cEq oEq ccEq
  refine ⟨tgtState t.code s.compileOracle s.compile { rst with locals := loc' }, frame, ⟨?_, ?_, ?_⟩, ?_⟩
  · show WordSemStateFiniteExact.LrPost temp res rst.locals loc'
    rcases res with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> exact h2
  · simp only [tgtState]; rw [cEq]; exact hcode
  · simp only [tgtState]; rw [← oEq, ← ccEq]
  · rw [wordCost_leaf _ (cscLeaf_isLeaf hp), wordCost_leaf _ (cscLeaf_isLeaf hp),
      optimizerPrice_state p t s]
    exact optimizer_le_preIsel p s

#print axioms isel_leaf_transfer
end InitECandidate.Runtime.FineCost
