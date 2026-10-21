import InitECandidate.Runtime.SSATailCallExecutedCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

open Classical in
/-- The pinned tail semantics with its actual scheduler witness exposed.
This repeats the original derivation only to retain the witness needed for
quantitative composition; no target execution is supplied by a caller. -/
theorem ssa_tail_fixed_semantics {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next))
        (.call none dest args handler : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    let sr := WordSemStateFiniteExact.evaluate (.call none dest args handler) {source with permute := target.permute}
    if sr.1 = some .error then True else
      let compiled := ssaCcTrans (.call none dest args handler) ssa next tables
      let tr := WordSemStateFiniteExact.evaluate compiled.1 target
      sr.1 = tr.1 ∧ Flapjack.WordAlloc.wordStateEqRel sr.2 tr.2 ∧
        match sr.1 with
        | none => ssaLocalsRel compiled.2.2 compiled.2.1 sr.2.locals tr.2.locals
        | some (.break n) => match tables[n]? with
          | none => True
          | some (dest, _, exits) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup dest) (sptDomain exits) sr.2.locals tr.2.locals
        | some (.continue n) => match tables[n]? with
          | none => True
          | some (dest, entries, _) => Flapjack.WordAlloc.strongLocalsRel
              (optionLookup dest) (sptDomain entries) sr.2.locals tr.2.locals
        | some _ => sr.2.locals = tr.2.locals := by
  classical
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  change let sr := WordSemStateFiniteExact.evaluate (.call none dest args handler) permuted
         if sr.1 = some .error then True else
           let compiled := ssaCcTrans (.call none dest args handler) ssa next tables
           let tr := WordSemStateFiniteExact.evaluate compiled.1 target
           sr.1 = tr.1 ∧ Flapjack.WordAlloc.wordStateEqRel sr.2 tr.2 ∧
             match sr.1 with
             | none => ssaLocalsRel compiled.2.2 compiled.2.1 sr.2.locals tr.2.locals
             | some (.break n) => match tables[n]? with
               | none => True
               | some (dest,_,exits) => Flapjack.WordAlloc.strongLocalsRel
                   (optionLookup dest) (sptDomain exits) sr.2.locals tr.2.locals
             | some (.continue n) => match tables[n]? with
               | none => True
               | some (dest,entries,_) => Flapjack.WordAlloc.strongLocalsRel
                   (optionLookup dest) (sptDomain entries) sr.2.locals tr.2.locals
             | some _ => sr.2.locals = tr.2.locals
  cases read : WordSemStateFiniteExact.getVars args permuted with
  | none => simp [WordSemStateFiniteExact.evaluate, read]
  | some values =>
    by_cases bad : wordSemBadDestArgs dest args = true
    · simp [WordSemStateFiniteExact.evaluate, read, bad]
    have good : wordSemBadDestArgs dest args = false := Bool.eq_false_iff.mpr bad
    cases found : wordSemFindCode dest values permuted.code permuted.stackSize with
    | none => simp [WordSemStateFiniteExact.evaluate, read, good, wordSemAddRetLoc, found]
    | some triple =>
      obtain ⟨calleeArgs,callee,size⟩ := triple
      cases handler with
      | some handler => simp [WordSemStateFiniteExact.evaluate, read, good, wordSemAddRetLoc, found]
      | none =>
        let renamed := args.map (optionLookup ssa)
        let registers := (List.range renamed.length).map fun key => 2 * key
        let moved := WordSemStateFiniteExact.setVars registers values target
        have preparation := ssa_tail_arguments permuted target ssa next args values h.2.1 read
        have moveRun : WordSemStateFiniteExact.evaluate (.move 1 (registers.zip renamed)) target =
            (none,moved) := preparation.1
        have reread : WordSemStateFiniteExact.getVars registers moved = some values := preparation.2
        have guard : wordSemBadDestArgs dest registers = false := by
          rw [ssa_tail_destination_guard]; exact good
        have movedFrame : Flapjack.WordAlloc.wordStateEqRel permuted moved := by
          simpa [moved,WordSemStateFiniteExact.setVars,Flapjack.WordAlloc.wordStateEqRel] using frame
        have fields := movedFrame
        unfold Flapjack.WordAlloc.wordStateEqRel at fields
        have codeEq := fields.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have sizeEq := fields.2.2.2.2.2.2.1
        have clockEq := fields.2.2.2.2.2.2.2.2.2.2.2.2.1
        have calleeState : WordSemStateFiniteExact.callEnv calleeArgs size
            (WordSemStateFiniteExact.decClock moved) =
            WordSemStateFiniteExact.callEnv calleeArgs size
              (WordSemStateFiniteExact.decClock permuted) := by
          simpa [permuted,moved,WordSemStateFiniteExact.setVars] using
            Flapjack.WordAlloc.callEnv_decClock_wsr movedFrame calleeArgs size
        have compiled : ssaCcTrans (width := width) (.call none dest args none) ssa next tables =
            (.seq (.move 1 (registers.zip renamed)) (.call none dest registers none),ssa,next) := rfl
        have seqRun : WordSemStateFiniteExact.evaluate
            (.seq (.move 1 (registers.zip renamed)) (.call none dest registers none)) target =
            WordSemStateFiniteExact.evaluate (.call none dest registers none) moved := by
          rw [WordSemStateFiniteExact.evaluate,moveRun]
          have fixed : target.fixClock ((none : Option (WordSemResult width)),moved) = (none,moved) := by
            simp [WordSemStateFiniteExact.fixClock,moved,WordSemStateFiniteExact.setVars]
          rw [fixed]
        simp only [compiled,seqRun]
        simp only [WordSemStateFiniteExact.evaluate,read,reread,good,guard,
          Bool.false_eq_true,if_false,wordSemAddRetLoc,codeEq,sizeEq,found,clockEq,calleeState]
        by_cases zero : permuted.clock = 0
        · simp only [zero]
          simp [WordSemStateFiniteExact.flushState,Flapjack.WordAlloc.wordStateEqRel]
          tauto
        · simp only [zero]
          cases run : WordSemStateFiniteExact.evaluate callee
              (WordSemStateFiniteExact.callEnv calleeArgs size (WordSemStateFiniteExact.decClock permuted)) with
          | mk result after =>
            cases result with
            | none => simp [wordSemBadFunReturn]
            | some result => cases result <;> simp [wordSemBadFunReturn,Flapjack.WordAlloc.wordStateEqRel]


/-- Complete quantitative tail-call SSA case, including semantics and cost
at the same source scheduler. No callee compiler induction premise remains. -/
theorem ssa_quantitative_tail {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (source target : WordSemStateFiniteExact 64 C F)
    (map : Spt Nat) (next : Nat) (dest : Option Nat) (args : List Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next map source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (width := 64) (fun x => decide (x < next)) (.call none dest args none) = true ∧
      ssaMapOK next map ∧ ltOK tables)
    (prices : ∀ p, TP p ≤ SP p)
    (localPrice : ssaTailLocalPrice TP dest args map ≤ SP (.call none dest args none)) :
    SSAQuantitativeSimulation SP TP (.call none dest args none) source target map next tables := by
  refine ⟨target.permute, ?_⟩
  dsimp only
  by_cases error : (evaluate (.call none dest args none) {source with permute := target.permute}).1 = some .error
  · exact Or.inl error
  · right
    have related := ssa_tail_fixed_semantics source target map next dest args none tables h
    dsimp only at related
    simp only [error, if_false] at related
    refine ⟨related.1, related.2.1, ?_, ?_⟩
    · have locals := related.2.2
      generalize resultEq : (evaluate (.call none dest args none) {source with permute := target.permute}).1 = outcome at locals ⊢
      cases outcome with
      | none => exact locals
      | some value => cases value <;> exact locals
    · exact ssa_tail_call_executed_cost SP TP source target map next dest args tables h.1 h.2.1 prices localPrice error

#print axioms ssa_tail_fixed_semantics
#print axioms ssa_quantitative_tail
end InitECandidate.Runtime.FineCost
