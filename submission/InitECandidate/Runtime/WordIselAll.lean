import InitECandidate.Runtime.WordIselRetCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-! The instruction-selection transfer for whole programs. `isel_goal` assembles
the leaf, statement, compound, loop and call cases by recursion on program
size; `isel_body_cost` is the endpoint for one function body, given callee runs
lexicographically below its start state. A global induction on
(termination depth, clock) discharges the callee hypothesis from this endpoint
for every body of an install-free code table. -/

/-- A tail call with a handler only errs. -/
theorem isel_call_none_handler {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (td ck temp : Nat)
    (dest : Option Nat) (args : List Nat) (hd : Nat × WordLangProgHOL (BitVec 64) × Nat × Nat) :
    IselGoal (C := C) (F := F) c td ck temp (.call none dest args (some hd)) := by
  intro ih s t res rst le vars rel run ok
  exfalso
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht] at run
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · simp only [hg, Prod.mk.injEq] at run; exact ok run.1.symm
  simp only [hg] at run
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true, Prod.mk.injEq] at run; exact ok run.1.symm
  simp only [hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc] at run
  rcases hf : wordSemFindCode dest xs s.code s.stackSize with _ | ⟨a1, pr, ss⟩
  · simp only [hf, Prod.mk.injEq] at run; exact ok run.1.symm
  · simp only [hf, Prod.mk.injEq] at run; exact ok run.1.symm

/-- The instruction-selection transfer for every install-free program, given
the callee hypothesis at the guard. -/
theorem isel_goal {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (td ck temp : Nat) :
    ∀ p : WordLangProgHOL (BitVec 64), installFree p = true → IselGoal (C := C) (F := F) c td ck temp p
  | .seq a b, h => by
    simp only [installFree, Bool.and_eq_true] at h
    exact isel_seq_step c td ck temp a b (isel_goal c td ck temp a h.1) (isel_goal c td ck temp b h.2)
  | .ite cmp r ri a b, h => by
    simp only [installFree, Bool.and_eq_true] at h
    exact isel_ite_step c td ck temp cmp r ri a b (isel_goal c td ck temp a h.1) (isel_goal c td ck temp b h.2)
  | .mustTerminate b, h => by
    simp only [installFree] at h
    exact isel_mustTerminate_step c td ck temp b (isel_goal c td ck temp b h)
  | .loop names b exitNames, h => by
    simp only [installFree] at h
    exact isel_loop_step c td ck temp names b exitNames (isel_goal c td ck temp b h)
  | .call none dest args none, _ => isel_tailcall c td ck temp dest args
  | .call none dest args (some hd), _ => isel_call_none_handler c td ck temp dest args hd
  | .call (some (n, names, k, l1, l2)) dest args none, h => by
    simp only [installFree, Bool.and_eq_true] at h
    exact isel_retcall c td ck temp n names k l1 l2 dest args none (isel_goal c td ck temp k h.1)
      (fun _ _ _ _ e => by cases e)
  | .call (some (n, names, k, l1, l2)) dest args (some (nn, hp, h1, h2)), h => by
    simp only [installFree, Bool.and_eq_true] at h
    exact isel_retcall c td ck temp n names k l1 l2 dest args (some (nn, hp, h1, h2)) (isel_goal c td ck temp k h.1)
      (fun _ _ _ _ e => by cases e; exact isel_goal c td ck temp hp h.2)
  | .assign v e, _ => fun _ s t res rst _ vars rel run ok =>
    isel_assign_transfer c temp s t res rst v e vars rel run ok
  | .set st e, _ => fun _ s t res rst _ vars rel run ok =>
    isel_set_transfer c temp s t res rst st e vars rel run ok
  | .store e v, _ => fun _ s t res rst _ vars rel run ok =>
    isel_store_transfer c temp s t res rst e v vars rel run ok
  | .shareInst op v e, _ => fun _ s t res rst _ vars rel run ok =>
    isel_shareInst_transfer c temp s t res rst op v e vars rel run ok
  | .install _ _ _ _ _, h => by simp [installFree] at h
  | .skip, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.skip) = (.skip) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .move a b, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.move a b) = (.move a b) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .inst a, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.inst a) = (.inst a) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .get a b, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.get a b) = (.get a b) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .alloc a b, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.alloc a b) = (.alloc a b) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .storeConsts a b d e f, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.storeConsts a b d e f) = (.storeConsts a b d e f) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .raise a, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.raise a) = (.raise a) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .«return» a b, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.«return» a b) = (.«return» a b) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .«break» a, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.«break» a) = (.«break» a) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .«continue» a, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.«continue» a) = (.«continue» a) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .opCurrHeap a b d, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.opCurrHeap a b d) = (.opCurrHeap a b d) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .tick, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.tick) = (.tick) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .locValue a b, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.locValue a b) = (.locValue a b) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .codeBufferWrite a b, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.codeBufferWrite a b) = (.codeBufferWrite a b) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .dataBufferWrite a b, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.dataBufferWrite a b) = (.dataBufferWrite a b) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
  | .ffi a b d e f g, _ => fun _ s t res rst _ vars rel run ok => by
    have sel : WordInst.instSelectExecutable c temp (.ffi a b d e f g) = (.ffi a b d e f g) := by
      simp [WordInst.instSelectExecutable]
    rw [sel]
    exact isel_leaf_transfer c temp _ rfl s t res rst vars rel run ok
termination_by p => sizeOf p

/-- Instruction selection of one install-free body over the mapped code table:
same result, related final state, and executed cost at the optimizer price at
most the source cost at the pre-selection price. -/
theorem isel_body_cost {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (p : WordLangProgHOL (BitVec 64)) (noInstall : installFree p = true)
    (s t : WordSemStateFiniteExact 64 C F) (res : Option (WordSemResult 64)) (rst : WordSemStateFiniteExact 64 C F)
    (ih : IselCalleeIH (C := C) (F := F) c s.termdep s.clock)
    (vars : everyVarHOL (fun x => decide (x < temp)) p = true) (rel : IselRel c temp s t)
    (run : evaluate p s = (res, rst)) (ok : res ≠ some .error) :
    ∃ rstT, evaluate (WordInst.instSelectExecutable c temp p) t = (res, rstT) ∧
      IselPost c temp res rst rstT ∧
      wordExecutionCost wordOptimizerLocalPrice (WordInst.instSelectExecutable c temp p) t ≤
        wordExecutionCost preIselPrice p s :=
  isel_goal c s.termdep s.clock temp p noInstall ih s t res rst (Or.inr ⟨rfl, Nat.le_refl _⟩) vars rel run ok

#print axioms isel_call_none_handler
#print axioms isel_goal
#print axioms isel_body_cost
end InitECandidate.Runtime.FineCost
