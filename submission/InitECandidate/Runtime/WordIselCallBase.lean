import InitECandidate.Runtime.WordIselLoop
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-! Call-case facts for the instruction-selection transfer: code lookups resolve
to selected bodies across `IselCode`, and the state operations of a call
(`decClock`, `pushEnv`, `callEnv`, `popEnv`, `setVar(s)`, `flushState`,
`getVars`) respect states that differ only in locals and code. -/

/-- A code lookup in the source table resolves, in the target table, to the
selected body at its fresh temporary. -/
theorem findCode_rel {c : Compiler.Encoders.Asm.AsmConfigExact 64}
    {src tgt : Spt (Nat × WordLangProgHOL (BitVec 64))} (h : IselCode c src tgt)
    {dest : Option Nat} {args : List (WordLocW 64)} {ss : Spt Nat}
    {args1 : List (WordLocW 64)} {prog : WordLangProgHOL (BitVec 64)} {ss' : Option Nat}
    (found : wordSemFindCode dest args src ss = some (args1, prog, ss')) :
    ∃ label arity tempF, sptLookup label src = some (arity, prog) ∧
      everyVarHOL (fun x => decide (x < tempF)) prog = true ∧
      sptLookup label tgt = some (arity, WordInst.instSelectExecutable c tempF prog) ∧
      wordSemFindCode dest args tgt ss = some (args1, WordInst.instSelectExecutable c tempF prog, ss') := by
  cases dest with
  | some p =>
    simp only [wordSemFindCode] at found ⊢
    rcases hl : sptLookup p src with _ | ⟨arity, body⟩
    · rw [hl] at found; cases found
    rw [hl] at found
    simp only at found
    split at found
    · rename_i hlen
      simp only [Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl, rfl⟩ := found
      obtain ⟨tempF, vars, ht⟩ := (h p).2 arity body hl
      exact ⟨p, arity, tempF, hl, vars, ht, by rw [ht]; simp [hlen]⟩
    · cases found
  | none =>
    simp only [wordSemFindCode] at found ⊢
    split at found
    · cases found
    · rename_i hne
      rw [dif_neg hne]
      split at found
      · rename_i loc heq
        rcases hl : sptLookup loc src with _ | ⟨arity, body⟩
        · rw [hl] at found; cases found
        rw [hl] at found
        simp only at found
        split at found
        · rename_i hlen
          simp only [Option.some.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, rfl, rfl⟩ := found
          obtain ⟨tempF, vars, ht⟩ := (h loc).2 arity body hl
          exact ⟨loc, arity, tempF, hl, vars, ht, by rw [ht]; simp [hlen]⟩
        · cases found
      · cases found

/-- `t` is `s` up to locals and code. -/
def UpToLC {C F : Type} (s t : WordSemStateFiniteExact 64 C F) : Prop :=
  t = { s with locals := t.locals, code := t.code }

theorem upToLC_decClock {C F : Type} {s t : WordSemStateFiniteExact 64 C F} (h : UpToLC s t) :
    UpToLC (decClock s) (decClock t) := by
  unfold UpToLC at *; simp only [decClock]; conv_lhs => rw [h]

theorem upToLC_callEnv {C F : Type} {s t : WordSemStateFiniteExact 64 C F} (h : UpToLC s t)
    (args : List (WordLocW 64)) (ss : Option Nat) :
    UpToLC (WordSemStateFiniteExact.callEnv args ss s) (WordSemStateFiniteExact.callEnv args ss t) ∧ (WordSemStateFiniteExact.callEnv args ss t).locals = (WordSemStateFiniteExact.callEnv args ss s).locals := by
  unfold UpToLC at *
  constructor
  · simp only [WordSemStateFiniteExact.callEnv]; conv_lhs => rw [h]
  · simp only [WordSemStateFiniteExact.callEnv]

theorem upToLC_flush {C F : Type} {s t : WordSemStateFiniteExact 64 C F} (h : UpToLC s t) (b : Bool) :
    UpToLC (flushState b s) (flushState b t) ∧ (flushState b t).locals = (flushState b s).locals := by
  unfold UpToLC at *
  cases b <;> constructor <;> simp only [flushState] <;> first | rfl | (conv_lhs => rw [h])

theorem upToLC_pushEnv {C F : Type} {s t : WordSemStateFiniteExact 64 C F} (h : UpToLC s t)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64)) (hd : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) :
    UpToLC (pushEnv envs hd s) (pushEnv envs hd t) := by
  unfold UpToLC at *
  cases hd <;> simp only [pushEnv] <;> conv_lhs => rw [h]

theorem pushEnv_handler_code {C F : Type} (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (n : Nat) (p q : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (s : WordSemStateFiniteExact 64 C F) :
    pushEnv envs (some (n, p, l1, l2)) s = pushEnv envs (some (n, q, l1, l2)) s := rfl

theorem upToLC_popEnv {C F : Type} {s t p : WordSemStateFiniteExact 64 C F} (h : UpToLC s t)
    (hp : popEnv s = some p) :
    popEnv t = some { p with code := t.code } ∧ UpToLC p { p with code := t.code } := by
  unfold UpToLC at *
  refine ⟨?_, rfl⟩
  have hs : t.stack = s.stack := by rw [h]
  unfold popEnv at hp ⊢
  rw [hs]
  split at hp
  · simp only [Option.some.injEq] at hp; subst hp; conv_lhs => rw [h]
  · simp only [Option.some.injEq] at hp; subst hp; conv_lhs => rw [h]
  · cases hp

theorem upToLC_setVars {C F : Type} {s t : WordSemStateFiniteExact 64 C F} (h : UpToLC s t)
    (hl : t.locals = s.locals) (ns : List Nat) (vs : List (WordLocW 64)) :
    UpToLC (setVars ns vs s) (setVars ns vs t) ∧ (setVars ns vs t).locals = (setVars ns vs s).locals := by
  unfold UpToLC at *
  constructor
  · simp only [setVars]; rw [hl]; conv_lhs => rw [h]
  · simp only [setVars, hl]

theorem upToLC_setVar {C F : Type} {s t : WordSemStateFiniteExact 64 C F} (h : UpToLC s t)
    (hl : t.locals = s.locals) (n : Nat) (v : WordLocW 64) :
    UpToLC (setVar n v s) (setVar n v t) ∧ (setVar n v t).locals = (setVar n v s).locals := by
  unfold UpToLC at *
  constructor
  · simp only [setVar]; rw [hl]; conv_lhs => rw [h]
  · simp only [setVar, hl]

theorem getVars_code {C F : Type} (X : WordSemStateFiniteExact 64 C F)
    (k : Spt (Nat × WordLangProgHOL (BitVec 64))) :
    ∀ args : List Nat, WordSemStateFiniteExact.getVars args { X with code := k } =
      WordSemStateFiniteExact.getVars args X
  | [] => rfl
  | a :: as => by
    have ga : getVar a { X with code := k } = getVar a X := rfl
    simp only [WordSemStateFiniteExact.getVars, ga, getVars_code X k as]

theorem getVars_rel {C F : Type} {c : Compiler.Encoders.Asm.AsmConfigExact 64} {temp : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (rel : IselRel c temp s t) (args : List Nat)
    (hargs : ∀ x ∈ args, x < temp) :
    WordSemStateFiniteExact.getVars args t = WordSemStateFiniteExact.getVars args s := by
  have base := locals_rel_get_vars_simp args temp s t.locals ⟨hargs, rel.1⟩
  have tx : t = { ({ s with locals := t.locals } : WordSemStateFiniteExact 64 C F) with code := t.code } := rel.2.2
  calc WordSemStateFiniteExact.getVars args t
      = WordSemStateFiniteExact.getVars args
          { ({ s with locals := t.locals } : WordSemStateFiniteExact 64 C F) with code := t.code } := by
        conv_lhs => rw [tx]
    _ = _ := (getVars_code _ _ args).trans base

#print axioms findCode_rel
#print axioms upToLC_popEnv
#print axioms getVars_rel
#print axioms findCode_rel
#print axioms upToLC_popEnv
#print axioms getVars_rel
#print axioms findCode_rel
#print axioms upToLC_popEnv
#print axioms getVars_rel
end InitECandidate.Runtime.FineCost
