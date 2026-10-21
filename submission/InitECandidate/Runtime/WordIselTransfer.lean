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
proves the leaf case and the expression statements. -/

/-- Programs without `install` (the only node that rewrites the code table). -/
def installFree : WordLangProgHOL (BitVec 64) → Bool
  | .install _ _ _ _ _ => false
  | .seq a b => installFree a && installFree b
  | .ite _ _ _ a b => installFree a && installFree b
  | .loop _ b _ => installFree b
  | .mustTerminate b => installFree b
  | .call ret _ _ h =>
    (match ret with | some (_, _, k, _, _) => installFree k | none => true) &&
    (match h with | some (_, hp, _, _) => installFree hp | none => true)
  | _ => true

/-- The target code table is the source table with every function body
instruction-selected at its own fresh temporary; every source body is
install-free, so the code table never changes during a run. -/
def IselCode (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (src tgt : Spt (Nat × WordLangProgHOL (BitVec 64))) : Prop :=
  ∀ dest, (sptLookup dest src = none ↔ sptLookup dest tgt = none) ∧
    ∀ arity body, sptLookup dest src = some (arity, body) →
      ∃ tempF, everyVarHOL (fun x => decide (x < tempF)) body = true ∧
        sptLookup dest tgt = some (arity, WordInst.instSelectExecutable c tempF body) ∧
        installFree body = true

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

theorem lineBound_seq_congr {leaf : WordLangProgHOL (BitVec 64) → Option Nat} {a b a' b' : WordLangProgHOL (BitVec 64)}
    (ha : lineBound leaf a' = lineBound leaf a) (hb : lineBound leaf b' = lineBound leaf b) :
    lineBound leaf (.seq a' b') = lineBound leaf (.seq a b) := by
  simp only [lineBound, ha, hb]

theorem leafX_inst (i j : WordLangInst (BitVec 64))
    (h : WordToStack.refinedNativeInstructionPrice (Compiler.Encoders.Asm.HolInst.ofWordLangInst i) =
      WordToStack.refinedNativeInstructionPrice (Compiler.Encoders.Asm.HolInst.ofWordLangInst j)) :
    lineBound preAllocLeafBudget (.inst i) = lineBound preAllocLeafBudget (.inst j) := by
  simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget, h]

/-- The line bound of selected code does not depend on the register names
`tar`/`temp`: every selection choice depends on the expression only. -/
theorem iselExp_lineBound_regs (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : WordLangExpHOL (BitVec 64)) :
    ∀ (tar temp X Y : Nat),
      lineBound preAllocLeafBudget (WordInst.instSelectExp c X Y e) =
        lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp e) := by
  refine (measure (sizeOf : WordLangExpHOL (BitVec 64) → Nat)).wf.induction (C := fun e => ∀ (tar temp X Y : Nat),
      lineBound preAllocLeafBudget (WordInst.instSelectExp c X Y e) =
        lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp e)) e ?_
  intro e ih tar temp X Y
  have ih' : ∀ e', sizeOf e' < sizeOf e → ∀ tar temp X Y : Nat,
      lineBound preAllocLeafBudget (WordInst.instSelectExp c X Y e') =
        lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp e') := fun e' h => ih e' h
  clear ih
  cases e
  case const w => rw [WordInst.instSelectExp, WordInst.instSelectExp]; exact leafX_inst _ _ rfl
  case var v =>
    rw [WordInst.instSelectExp, WordInst.instSelectExp]
    simp [lineBound, isLeafProg, preAllocLeafBudget, rawMovePrice]
  case lookup st =>
    rw [WordInst.instSelectExp, WordInst.instSelectExp]
    simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget]
  case load exp =>
    rw [WordInst.instSelectExp.eq_def, WordInst.instSelectExp.eq_def]
    simp only
    split
    · rename_i exp' w
      split_ifs
      · exact lineBound_seq_congr (ih' exp' (by simp; omega) _ _ _ _) (leafX_inst _ _ rfl)
      · exact lineBound_seq_congr (ih' _ (by simp) _ _ _ _) (leafX_inst _ _ rfl)
    · exact lineBound_seq_congr (ih' exp (by simp) _ _ _ _) (leafX_inst _ _ rfl)
  case op op args =>
    rcases args with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, rest⟩⟩⟩
    · rw [WordInst.instSelectExp, WordInst.instSelectExp] <;> (intros; simp_all)
    · rw [WordInst.instSelectExp, WordInst.instSelectExp] <;> (intros; simp_all)
    · rw [WordInst.instSelectExp.eq_def, WordInst.instSelectExp.eq_def]
      simp only
      split_ifs
      · exact lineBound_seq_congr (ih' e1 (by simp; omega) _ _ _ _)
          (by simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget])
      · exact lineBound_seq_congr (ih' e2 (by simp; omega) _ _ _ _)
          (by simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget])
      · split
        · split_ifs
          · exact lineBound_seq_congr (ih' e1 (by simp; omega) _ _ _ _) (leafX_inst _ _ rfl)
          · exact lineBound_seq_congr (ih' e1 (by simp; omega) _ _ _ _) (leafX_inst _ _ rfl)
          · exact lineBound_seq_congr (ih' e1 (by simp; omega) _ _ _ _)
              (lineBound_seq_congr (leafX_inst _ _ rfl) (leafX_inst _ _ rfl))
        · exact lineBound_seq_congr (ih' e1 (by simp; omega) _ _ _ _)
            (lineBound_seq_congr (ih' e2 (by simp; omega) _ _ _ _) (leafX_inst _ _ rfl))
    · rw [WordInst.instSelectExp, WordInst.instSelectExp] <;> (intros; simp_all)
  case shift sh exp e1 =>
    rw [WordInst.instSelectExp.eq_def, WordInst.instSelectExp.eq_def]
    simp only
    split
    · split_ifs
      · exact lineBound_seq_congr (ih' exp (by simp; omega) _ _ _ _)
          (by simp [lineBound, isLeafProg, preAllocLeafBudget, rawMovePrice])
      · exact lineBound_seq_congr (ih' exp (by simp; omega) _ _ _ _) (leafX_inst _ _ rfl)
      · exact leafX_inst _ _ rfl
    · exact lineBound_seq_congr (ih' exp (by simp; omega) _ _ _ _)
        (lineBound_seq_congr (ih' e1 (by simp) _ _ _ _) (leafX_inst _ _ rfl))
/-- Statements selected through an expression: `assign`, `set`, `store`, `shareInst`. -/
def isExprStmt : WordLangProgHOL (BitVec 64) → Bool
  | .assign _ _ | .set _ _ | .store _ _ | .shareInst _ _ _ => true
  | _ => false

/-- Whole expression statements: the selected code's line bound does not
depend on the temporary. -/
theorem iselStmt_lineBound_temp (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (p : WordLangProgHOL (BitVec 64)) (hp : isExprStmt p = true) :
    lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp p) =
      lineBound preAllocLeafBudget (WordInst.instSelectExecutable c 0 p) := by
  cases p <;> simp only [isExprStmt, Bool.false_eq_true] at hp
  case assign v e =>
    simp only [WordInst.instSelectExecutable]
    exact (iselExp_lineBound_regs c _ v 0 v temp).trans rfl
  case set st e =>
    simp only [WordInst.instSelectExecutable]
    exact lineBound_seq_congr (iselExp_lineBound_regs c _ 0 0 temp temp)
      (by simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget])
  case store e v =>
    simp only [WordInst.instSelectExecutable]
    split
    · split_ifs
      · exact lineBound_seq_congr (iselExp_lineBound_regs c _ 0 0 temp temp) (leafX_inst _ _ rfl)
      · exact lineBound_seq_congr (iselExp_lineBound_regs c _ 0 0 temp temp) (leafX_inst _ _ rfl)
    · exact lineBound_seq_congr (iselExp_lineBound_regs c _ 0 0 temp temp) (leafX_inst _ _ rfl)
  case shareInst op v e =>
    simp only [WordInst.instSelectExecutable]
    split
    · split_ifs
      · exact lineBound_seq_congr (iselExp_lineBound_regs c _ 0 0 temp temp)
          (by simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget])
      · exact lineBound_seq_congr (iselExp_lineBound_regs c _ 0 0 temp temp)
          (by simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget])
    · exact lineBound_seq_congr (iselExp_lineBound_regs c _ 0 0 temp temp)
        (by simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget])

/-- Exact selected-code cost of an expression statement (temporary-independent). -/
def iselX (c : Compiler.Encoders.Asm.AsmConfigExact 64) (p : WordLangProgHOL (BitVec 64)) : Nat :=
  (lineBound preAllocLeafBudget (WordInst.instSelectExecutable c 0 p)).getD 0

/-- Pre-selection price: an expression statement pays exactly the static
line bound of its own selected code; every other node pays
`wordOptimizerLocalPrice`. -/
noncomputable def preIselPrice {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) : Nat :=
  match p with
  | .assign _ _ | .set _ _ | .store _ _ | .shareInst _ _ _ => iselX c p
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
        wordExecutionCost (preIselPrice c) body s

section
attribute [local simp] lineBound isLeafProg preAllocLeafBudget rawMovePrice
  WordToStack.refinedWordStackLeafBudget

theorem isel_shareInst_lineBound (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (op : WordMemOp) (v : Nat) (e : WordLangExpHOL (BitVec 64)) :
    ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp (.shareInst op v e)) = some k ∧
      k ≤ selExpCost e + 13 := by
  simp only [WordInst.instSelectExecutable, selExpCost]
  split
  · rename_i exp' w heq
    split
    · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp exp'
      refine ⟨k + 13, by simp [hk], ?_⟩
      rw [heq, iselCost_op2]; simp; omega
    · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp (.op .add [exp', .const w])
      exact ⟨k + 13, by rw [heq]; simp [hk], by rw [heq]; omega⟩
  · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp
      (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e))
    exact ⟨k + 13, by simp [hk], by omega⟩
end

/-- `iselX` is the line bound of the selected code at every temporary. -/
theorem iselX_line (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat) (p : WordLangProgHOL (BitVec 64))
    (hp : isExprStmt p = true) :
    lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp p) = some (iselX c p) := by
  rw [iselStmt_lineBound_temp c temp p hp, iselX]
  have ex : ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExecutable c 0 p) = some k := by
    cases p <;> simp only [isExprStmt, Bool.false_eq_true] at hp
    case assign v e => obtain ⟨k, hk, -⟩ := isel_assign_lineBound c 0 v e; exact ⟨k, hk⟩
    case set st e => obtain ⟨k, hk, -⟩ := isel_set_lineBound c 0 st e; exact ⟨k, hk⟩
    case store e v => obtain ⟨k, hk, -⟩ := isel_store_lineBound c 0 v e; exact ⟨k, hk⟩
    case shareInst op v e => obtain ⟨k, hk, -⟩ := isel_shareInst_lineBound c 0 op v e; exact ⟨k, hk⟩
  obtain ⟨k, hk⟩ := ex
  rw [hk]; rfl

/-- The pre-selection price dominates the optimizer price on every node. -/
theorem optimizer_le_preIsel {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice p s ≤ preIselPrice c p s := by
  cases p <;> simp only [preIselPrice, Nat.le_refl]
  case set st e =>
    have h := iselX_line c 0 (.set st e) rfl
    simp only [WordInst.instSelectExecutable] at h
    obtain ⟨x, y, -, hy, hk⟩ := lineBound_seq h
    simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget] at hy
    rw [hk]
    simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]
    omega
  case shareInst op v e =>
    have h := iselX_line c 0 (.shareInst op v e) rfl
    simp only [WordInst.instSelectExecutable] at h
    split at h <;> (try split at h) <;>
    · obtain ⟨x, y, -, hy, hk⟩ := lineBound_seq h
      simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget] at hy
      rw [hk]
      simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]
      omega
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
      wordExecutionCost wordOptimizerLocalPrice p t ≤ wordExecutionCost (preIselPrice c) p s := by
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
    exact optimizer_le_preIsel c p s

#print axioms isel_leaf_transfer
open Flapjack.Compiler.Backend.WordToWord in
/-- A leaf whose selected code has a static cost within its pre-selection price
transfers: its selected code runs to the same result from the related target
state, over the target code table. -/
theorem isel_stmt_transfer {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (p : WordLangProgHOL (BitVec 64)) (hp : cscLeaf p = true) (s t : WordSemStateFiniteExact 64 C F)
    (res : Option (WordSemResult 64)) (rst : WordSemStateFiniteExact 64 C F)
    (k : Nat) (line : lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp p) = some k)
    (priced : k ≤ preIselPrice c p s)
    (vars : everyVarHOL (fun x => decide (x < temp)) p = true) (rel : IselRel c temp s t)
    (run : evaluate p s = (res, rst)) (ok : res ≠ some .error) :
    ∃ rstT, evaluate (WordInst.instSelectExecutable c temp p) t = (res, rstT) ∧
      IselPost c temp res rst rstT ∧
      wordExecutionCost wordOptimizerLocalPrice (WordInst.instSelectExecutable c temp p) t ≤
        wordExecutionCost (preIselPrice c) p s := by
  obtain ⟨hl, hcode, ht⟩ := rel
  -- the source run over the target code table
  have frame := evaluate_tgt_frame t.code s.compileOracle s.compile s (fun n => iselCode_mem hcode n) p hp
  rw [run] at frame
  obtain ⟨cEq, oEq, ccEq⟩ := leaf_frame_const p hp s
  rw [run] at cEq oEq ccEq
  -- selection on that state
  obtain ⟨loc', h1, h2⟩ := WordInst.inst_select_thm c temp p (tgtState t.code s.compileOracle s.compile s) res
    (tgtState t.code s.compileOracle s.compile rst) t.locals ⟨frame, vars, ok, hl⟩
  have tEq : { tgtState t.code s.compileOracle s.compile s with locals := t.locals } = t :=
    (rfl : { tgtState t.code s.compileOracle s.compile s with locals := t.locals } =
      { s with locals := t.locals, code := t.code }).trans ht.symm
  rw [tEq, ← WordInst.instSelectExecutable_eq] at h1
  refine ⟨_, h1, ⟨?_, ?_, ?_⟩, ?_⟩
  · show WordSemStateFiniteExact.LrPost temp res rst.locals loc'
    rcases res with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> exact h2
  · simp only [tgtState]; rw [cEq]; exact hcode
  · simp only [tgtState]; rw [← oEq, ← ccEq]
  · have bound := wordCost_le_lineBound wordOptimizerLocalPrice preAllocLeafBudget
      (fun a b s => by simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
        WordToStack.refinedWordStackLeafBudget])
      (fun q s n leaf budget => optimizerPrice_le_preAllocLeaf q s n leaf budget) _ k line t
    rw [wordCost_leaf _ (cscLeaf_isLeaf hp)]
    omega

theorem isel_assign_transfer {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (s t : WordSemStateFiniteExact 64 C F) (res : Option (WordSemResult 64))
    (rst : WordSemStateFiniteExact 64 C F) (v : Nat) (e : WordLangExpHOL (BitVec 64))
    (vars : everyVarHOL (fun x => decide (x < temp)) (.assign v e) = true) (rel : IselRel c temp s t)
    (run : evaluate (.assign v e) s = (res, rst)) (ok : res ≠ some .error) :
    ∃ rstT, evaluate (WordInst.instSelectExecutable c temp (.assign v e)) t = (res, rstT) ∧
      IselPost c temp res rst rstT ∧
      wordExecutionCost wordOptimizerLocalPrice (WordInst.instSelectExecutable c temp (.assign v e)) t ≤
        wordExecutionCost (preIselPrice c) (.assign v e) s := by
  exact isel_stmt_transfer c temp _ rfl s t res rst _ (iselX_line c temp _ rfl) (by simp [preIselPrice]) vars rel
    run ok

theorem isel_set_transfer {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (s t : WordSemStateFiniteExact 64 C F) (res : Option (WordSemResult 64))
    (rst : WordSemStateFiniteExact 64 C F) (st : WordStoreHOL) (e : WordLangExpHOL (BitVec 64))
    (vars : everyVarHOL (fun x => decide (x < temp)) (.set st e) = true) (rel : IselRel c temp s t)
    (run : evaluate (.set st e) s = (res, rst)) (ok : res ≠ some .error) :
    ∃ rstT, evaluate (WordInst.instSelectExecutable c temp (.set st e)) t = (res, rstT) ∧
      IselPost c temp res rst rstT ∧
      wordExecutionCost wordOptimizerLocalPrice (WordInst.instSelectExecutable c temp (.set st e)) t ≤
        wordExecutionCost (preIselPrice c) (.set st e) s := by
  exact isel_stmt_transfer c temp _ rfl s t res rst _ (iselX_line c temp _ rfl) (by simp [preIselPrice]) vars rel
    run ok

theorem isel_store_transfer {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (s t : WordSemStateFiniteExact 64 C F) (res : Option (WordSemResult 64))
    (rst : WordSemStateFiniteExact 64 C F) (e : WordLangExpHOL (BitVec 64)) (v : Nat)
    (vars : everyVarHOL (fun x => decide (x < temp)) (.store e v) = true) (rel : IselRel c temp s t)
    (run : evaluate (.store e v) s = (res, rst)) (ok : res ≠ some .error) :
    ∃ rstT, evaluate (WordInst.instSelectExecutable c temp (.store e v)) t = (res, rstT) ∧
      IselPost c temp res rst rstT ∧
      wordExecutionCost wordOptimizerLocalPrice (WordInst.instSelectExecutable c temp (.store e v)) t ≤
        wordExecutionCost (preIselPrice c) (.store e v) s := by
  exact isel_stmt_transfer c temp _ rfl s t res rst _ (iselX_line c temp _ rfl) (by simp [preIselPrice]) vars rel
    run ok

theorem isel_shareInst_transfer {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (s t : WordSemStateFiniteExact 64 C F) (res : Option (WordSemResult 64))
    (rst : WordSemStateFiniteExact 64 C F) (op : WordMemOp) (v : Nat) (e : WordLangExpHOL (BitVec 64))
    (vars : everyVarHOL (fun x => decide (x < temp)) (.shareInst op v e) = true) (rel : IselRel c temp s t)
    (run : evaluate (.shareInst op v e) s = (res, rst)) (ok : res ≠ some .error) :
    ∃ rstT, evaluate (WordInst.instSelectExecutable c temp (.shareInst op v e)) t = (res, rstT) ∧
      IselPost c temp res rst rstT ∧
      wordExecutionCost wordOptimizerLocalPrice (WordInst.instSelectExecutable c temp (.shareInst op v e)) t ≤
        wordExecutionCost (preIselPrice c) (.shareInst op v e) s := by
  exact isel_stmt_transfer c temp _ rfl s t res rst _ (iselX_line c temp _ rfl) (by simp [preIselPrice]) vars rel
    run ok

#print axioms isel_stmt_transfer
#print axioms isel_assign_transfer
#print axioms isel_set_transfer
#print axioms isel_store_transfer
#print axioms isel_shareInst_transfer
end InitECandidate.Runtime.FineCost
