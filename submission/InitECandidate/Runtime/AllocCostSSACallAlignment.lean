import InitECandidate.Runtime.AllocCostSSABodyWork
import InitECandidate.Runtime.AllocCostSSAPermStack
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallReturn
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordSemStateFiniteExact
open InitECandidate.Runtime.WordToStack

/-!
# Actual `ssaCcTrans` returning-call alignment

`AllocCostSSABodyWork` reduces the returning-call bound to a transfer at the
literal compiled program shape, taking the inserted stack move, the inserted
argument move, the renamed argument read, the renamed paired cut, the renamed
bad-shape test and the code lookup as hypotheses.  This module derives those
from the actual SSA conversion and the pinned public returning-call lemmas
(`returningRefreshArguments`, `returningPrepareArguments`), so that only the
genuinely callee-dependent facts (the compiled code lookup at the renamed
return locations, the callee result/pop correspondence and the body work
transfers) remain as premises.

The excluded-source-failure fact is proved as well: a call whose actual source
evaluation is not the `error` result cannot have a failing `getVars`, because
the literal `evaluate` call clause answers `some .error` in that case.
-/

/-- Literal `ssaCcTrans` output for a returning call without an exception
handler: the stack rename move, the argument move and the renamed call whose
return locations are the physical registers `2*(i+1)`. -/
theorem ssaCcTrans_call_returning_none_output
    (ret : List Nat) (numset : Spt Unit × Spt Unit)
    (retHandler : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (ssa : Spt Nat) (na : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)) :
    ssaCcTrans (width := 64) (.call (some (ret, numset, retHandler, l1, l2)) dest args none)
        ssa na tables =
      (let allNames := sptUnion numset.1 numset.2
       let ls := (sptToAList allNames).map Prod.fst
       let (stackMov, ssa', na') := listNextVarRenameMove (width := 64) ssa (na + 2) ls
       let stackSet := Flapjack.WordAlloc.applyNummapsKey (optionLookup ssa') numset
       let names := args.map (optionLookup ssa)
       let convArgs := (List.range names.length).map fun x => 2 * (x + 1)
       let moveArgs := WordLangProgHOL.move 1 (convArgs.zip names)
       let ssaCut := sptInter ssa' allNames
       let (retMov, ssa'', na'') := listNextVarRenameMove (width := 64) ssaCut (na' + 2) ls
       let (ret', ssa2p, na2p) := listNextVarRename ret ssa'' na''
       let (renRetHandler, ssa2, na2) := ssaCcTrans retHandler ssa2p na2p tables
       let regs := (List.range ret.length).map fun x => 2 * (x + 1)
       let movRetHandler := WordLangProgHOL.seq retMov
         (.seq (.move 1 (ret'.zip regs)) renRetHandler)
       (WordLangProgHOL.seq stackMov (.seq moveArgs
          (.call (some (regs, stackSet, movRetHandler, l1, l2)) dest convArgs none)),
        ssa2, na2)) := by
  simp only [ssaCcTrans]

/-- The renamed call's bad-shape test is the source one: `wordSemBadDestArgs`
only inspects whether `dest` and the argument list are simultaneously empty,
and the empty list test is preserved by the SSA renaming. -/
theorem wordSemBadDestArgs_renameArgs {dest : Option Nat} {args args' : List Nat}
    (h : args = [] ↔ args' = []) :
    wordSemBadDestArgs dest args = wordSemBadDestArgs dest args' := by
  simp only [wordSemBadDestArgs]
  by_cases hd : dest = none
  · by_cases ha : args' = []
    · have ha' : args = [] := h.mpr ha
      simp only [hd, ha, ha']
    · have ha' : args ≠ [] := fun hc => ha (h.mp hc)
      simp only [hd, ha, ha']
  · simp only [hd, false_and]

/-- The inserted stack rename move is a single parallel move, so it charges
exactly one control node of `wordPathWork`. -/
theorem wordPathWork_listNextVarRenameMove {C F : Type}
    (ssa : Spt Nat) (n : Nat) (ls : List Nat)
    (target : WordSemStateFiniteExact 64 C F) :
    wordPathWork (listNextVarRenameMove (width := 64) ssa n ls).1 target = 1 := by
  unfold listNextVarRenameMove
  cases listNextVarRename ls ssa n with
  | mk newLs rest => dsimp only; simp only [wordPathWork]

/-- Inserted stack-move/argument-move/paired-cut alignment for an actual
returning call.  From the public returning-call preparation lemma and the
literal `ssaCcTrans` constituents, the compiled program's two inserted moves
execute normally and charge one control node each, the renamed argument read
returns the same values, the renamed paired cut exists, the renamed bad-shape
test is the source one, and both the frame and the mapped locals relation are
preserved. -/
theorem ssaCallReturning_prepare_alignment {C F : Type}
    (source target : WordSemStateFiniteExact 64 C F) (ssa : Spt Nat) (na : Nat)
    (dest : Option Nat) (args : List Nat) (values : List (WordLocW 64))
    (numset : Spt Unit × Spt Unit) (sourceFirst sourceSecond : Spt (WordLocW 64))
    (stackMov : WordLangProgHOL (BitVec 64)) (mapOut : Spt Nat) (counter : Nat)
    (cut : wordSemCutEnvs numset source.locals = some (sourceFirst, sourceSecond))
    (read : getVars args source = some values)
    (related : ssaLocalsRel na ssa source.locals target.locals)
    (allocated : isAllocVar na) (valid : ssaMapOK na ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (bad : wordSemBadDestArgs dest args = false)
    (produced : listNextVarRenameMove (width := 64) ssa (na + 2)
      ((sptToAList (sptUnion numset.1 numset.2)).map Prod.fst) = (stackMov, mapOut, counter)) :
    let moveArgs := WordLangProgHOL.move 1
      (((List.range (args.map (optionLookup ssa)).length).map fun x => 2 * (x + 1)).zip
        (args.map (optionLookup ssa)))
    let refreshed := (evaluate stackMov target).2
    let prepared := setVars
      ((List.range (args.map (optionLookup ssa)).length).map fun x => 2 * (x + 1)) values refreshed
    (evaluate stackMov target).1 = none ∧
      evaluate stackMov target = (none, refreshed) ∧
      fixClock target (evaluate stackMov target) = (none, refreshed) ∧
      wordPathWork stackMov target = 1 ∧
      evaluate moveArgs refreshed = (none, prepared) ∧
      wordPathWork moveArgs refreshed = 1 ∧
      getVars ((List.range (args.map (optionLookup ssa)).length).map fun x => 2 * (x + 1))
        prepared = some values ∧
      wordSemBadDestArgs dest
        ((List.range (args.map (optionLookup ssa)).length).map fun x => 2 * (x + 1)) = false ∧
      (∃ envsT : Spt (WordLocW 64) × Spt (WordLocW 64),
        wordSemCutEnvs (Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) numset) prepared.locals =
          some envsT) ∧
      Flapjack.WordAlloc.wordStateEqRel source prepared ∧
      ssaLocalsRel counter mapOut source.locals prepared.locals := by
  dsimp only
  have prep := returningPrepareArguments (width := 64) source target ssa na args values
    numset.1 numset.2 sourceFirst sourceSecond cut read related allocated valid frame
  rw [produced] at prep
  dsimp only at prep
  obtain ⟨norm, runArg, readT, relatedT, frameT, tF, tS, cutT, -⟩ := prep
  have hfirst : (listNextVarRenameMove (width := 64) ssa (na + 2)
      ((sptToAList (sptUnion numset.1 numset.2)).map Prod.fst)).1 = stackMov := by
    rw [produced]
  have hnil : ((List.range (args.map (optionLookup ssa)).length).map fun x => 2 * (x + 1)) = [] ↔
      args = [] := by simp
  have hpair : evaluate stackMov target =
      ((evaluate stackMov target).1, (evaluate stackMov target).2) := rfl
  refine ⟨norm, ?_, ?_, ?_, runArg, ?_, readT, ?_, ⟨(tF, tS), ?_⟩, frameT, relatedT⟩
  · rw [hpair, norm]
  · obtain ⟨res, st, hev⟩ : ∃ res st, evaluate stackMov target = (res, st) := ⟨_, _, rfl⟩
    have hc : st.clock ≤ target.clock := by
      have h := (evaluate_clock_proj stackMov target).1
      rwa [hev] at h
    have ht : st.termdep = target.termdep := by
      have h := (evaluate_clock_proj stackMov target).2
      rwa [hev] at h
    have hn : res = none := by
      have h := norm
      rwa [hev] at h
    rw [hev]
    simp only [fixClock, if_neg (Nat.not_lt.mpr hc), hn]
    rw [← ht]
  · rw [← hfirst]
    exact wordPathWork_listNextVarRenameMove ssa (na + 2)
      ((sptToAList (sptUnion numset.1 numset.2)).map Prod.fst) target
  · simp only [wordPathWork]
  · rw [wordSemBadDestArgs_renameArgs hnil]
    exact bad
  · simpa using cutT

/-- A source call whose actual evaluation is not the `error` result cannot have
a failing `getVars`: the literal `evaluate` call clause answers `some .error`
as soon as `getVars` fails.  This replaces any inversion of the one-directional
`ssaLocalsRel`. -/
theorem sourceCall_getVars_some_of_not_error {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (res : WordSemResult 64)
    (s' : WordSemStateFiniteExact 64 C F)
    (run : evaluate (.call ret dest args handler) s = (some res, s'))
    (hres : res ≠ .error) :
    ∃ xs, getVars args s = some xs := by
  rcases hg : getVars args s with _ | xs
  · have hcall : evaluate (.call ret dest args handler) s = (some .error, s) := by
      simp only [evaluate, hg]
    rw [hcall] at run
    simp only [Prod.mk.injEq, Option.some.injEq] at run
    exact absurd run.1.symm hres
  · exact ⟨xs, rfl⟩

/-- Actual compiler returning-call case (no exception handler).  The literal
`ssaCcTrans` output is executed through the inserted stack move, the inserted
argument move, the renamed argument read, the renamed paired cut and the
renamed bad-shape test, all discharged by `ssaCallReturning_prepare_alignment`;
what remains is callee-dependent: the compiled code lookup at the physical
return registers, the callee result/pop correspondence at the renamed entry
state, and the two body work transfers (`calleeWork` is exactly the pending
body permutation transport, `retWork` the continuation transfer). -/
theorem ssaBody_call_returning_executed_le {C F : Type}
    (values : List Nat) (numset : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source target middle popped : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64)) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (args1 args1T : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat)
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (ssa : Spt Nat) (na : Nat)
    (stackMov : WordLangProgHOL (BitVec 64)) (mapOut : Spt Nat) (counter : Nat)
    (regs : List Nat) (stackSet : WordLangCutsetsHOL)
    (movRetHandler : WordLangProgHOL (BitVec 64)) (convArgs : List Nat)
    (handlerT : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (refreshed prepared middleT targetPopped : WordSemStateFiniteExact 64 C F)
    (valuesT : List (WordLocW 64)) (moveArgs : WordLangProgHOL (BitVec 64))
    (envsT : Spt (WordLocW 64) × Spt (WordLocW 64))
    (locationT : WordLocW 64) (returnedT : List (WordLocW 64))
    (calleeBudget retBudget : Nat)
    (read : getVars args source = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, numset, retCode, l1, l2)) xs) source.code
      source.stackSize = some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty numset.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs numset source.locals = some envs)
    (clock : source.clock ≠ 0)
    (run : fixClock (callEnv args1 ss (pushEnv envs none (decClock source)))
      (evaluate prog (callEnv args1 ss (pushEnv envs none (decClock source)))) =
      (some (.result location returned), middle))
    (pop : popEnv middle = some popped)
    (locEq : location = .loc l1 l2)
    (lenEq : returned.length = values.length)
    (domUnion : sptDomainEqUnion popped.locals envs.1 envs.2)
    (related : ssaLocalsRel na ssa source.locals target.locals)
    (allocated : isAllocVar na) (valid : ssaMapOK na ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (produced : listNextVarRenameMove (width := 64) ssa (na + 2)
      ((sptToAList (sptUnion numset.1 numset.2)).map Prod.fst) = (stackMov, mapOut, counter))
    (convEq : convArgs = (List.range (args.map (optionLookup ssa)).length).map
      fun x => 2 * (x + 1))
    (stackSetEq : stackSet = Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) numset)
    (moveEq : moveArgs = WordLangProgHOL.move 1 (convArgs.zip (args.map (optionLookup ssa))))
    (refEq : refreshed = (evaluate stackMov target).2)
    (prepEq : prepared = setVars convArgs xs refreshed)
    (valuesTEq : valuesT = xs)
    (findT : wordSemFindCode dest
      (wordSemAddRetLoc (some (regs, stackSet, movRetHandler, l1, l2)) valuesT)
      prepared.code prepared.stackSize = some (args1T, prog, ss))
    (domT : ¬ sptDomainEmpty stackSet.1) (nodupT : regs.Nodup)
    (cutT : wordSemCutEnvs stackSet prepared.locals = some envsT)
    (clockT : prepared.clock ≠ 0)
    (runT : fixClock (callEnv args1T ss (pushEnv envsT handlerT (decClock prepared)))
      (evaluate prog (callEnv args1T ss (pushEnv envsT handlerT (decClock prepared)))) =
      (some (.result locationT returnedT), middleT))
    (popT : popEnv middleT = some targetPopped)
    (locEqT : locationT = .loc l1 l2)
    (lenEqT : returnedT.length = regs.length)
    (domUnionT : sptDomainEqUnion targetPopped.locals envsT.1 envsT.2)
    (calleeWork : wordPathWork prog
      (callEnv args1T ss (pushEnv envsT handlerT (decClock prepared))) ≤
      wordPathWork prog (callEnv args1 ss (pushEnv envs none (decClock source))) + calleeBudget)
    (retWork : wordPathWork movRetHandler (setVars regs returnedT targetPopped) ≤
      wordPathWork retCode (setVars values returned popped) + retBudget) :
    wordPathWork (.seq stackMov
      (.seq moveArgs (.call (some (regs, stackSet, movRetHandler, l1, l2))
        dest convArgs handlerT))) target ≤
      wordPathWork (.call (some (values, numset, retCode, l1, l2)) dest args none) source +
        (calleeBudget + retBudget + 4) := by
  have align := ssaCallReturning_prepare_alignment source target ssa na dest args xs numset
    envs.1 envs.2 stackMov mapOut counter (by simpa using cut) read related allocated valid
    frame bad produced
  dsimp only at align
  rw [← convEq, ← stackSetEq, ← moveEq, ← refEq, ← prepEq] at align
  obtain ⟨-, -, stackFixed, stackWork, argFixed, argWork, getT0, badT, -, -, -⟩ := align
  have getT : getVars convArgs prepared = some valuesT := by
    rw [valuesTEq]
    exact getT0
  have hclk : prepared.clock = refreshed.clock := by
    rw [prepEq]; rfl
  have htrm : prepared.termdep = refreshed.termdep := by
    rw [prepEq]; rfl
  have argFixedFix : fixClock refreshed (evaluate moveArgs refreshed) = (none, prepared) := by
    rw [argFixed]
    simp only [fixClock, if_neg (Nat.not_lt.mpr (Nat.le_of_eq hclk)), ← htrm]
    try rfl
  exact bodyWork_call_returning_result values numset retCode l1 l2 dest args none source
    middle popped xs envs args1 args1T prog ss location returned read bad find dom nodup cut
    clock run pop locEq lenEq domUnion regs stackSet movRetHandler convArgs handlerT target
    refreshed prepared middleT targetPopped valuesT stackMov moveArgs envsT locationT returnedT
    stackFixed stackWork argFixedFix argWork getT badT findT domT nodupT cutT clockT runT popT
    locEqT lenEqT domUnionT calleeBudget retBudget calleeWork retWork

/-- Result/pop correspondence on the swapped stack.  From the source successful
`popEnv` and the callee stack-swap facts (key and value relations produced by
the body transport), the target stack swapped into the returned state pops
successfully, the two popped states are frame-related, and the popped source
cut domain and every target popped lookup are known.  This is the exact input
`bodyWork_call_returning_result` needs as `popT`, with the domain facts that
feed the union test. -/
theorem ssaCallReturning_pop_alignment {C F : Type}
    (source target returned : WordSemStateFiniteExact 64 C F)
    (first second targetFirst targetSecond : Spt (WordLocW 64))
    (handler targetHandler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (targetStack : List (WordSemStackFrame 64)) (f : Nat → Nat)
    (sourceRoots targetRoots : List (Nat × WordLocW 64))
    (sourcePerm targetPerm : Nat → Nat → Nat) (popped : WordSemStateFiniteExact 64 C F)
    (sourcePop : popEnv returned = some popped)
    (sameStack : source.stack = target.stack)
    (sourceRootRead : wordSemEnvToList second source.permute = (sourceRoots, sourcePerm))
    (targetRootRead : wordSemEnvToList targetSecond target.permute = (targetRoots, targetPerm))
    (rootMap : sourceRoots.map (fun (key, value) => (f key, value)) = targetRoots)
    (firstRelated : Flapjack.WordAlloc.strongLocalsRel f (sptDomain first) first targetFirst)
    (injective : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
      (sptDomain first b ∨ sptDomain second b) → f a = f b → a = b)
    (sourceKeys : WordSemStackEq.sKeyEq
      (pushEnv (first, second) handler source).stack returned.stack)
    (targetKeys : WordSemStackEq.sKeyEq
      (pushEnv (targetFirst, targetSecond) targetHandler target).stack targetStack)
    (stackValues : WordSemStackEq.sValEq returned.stack targetStack) :
    ∃ targetPopped : WordSemStateFiniteExact 64 C F,
      popEnv {returned with stack := targetStack} = some targetPopped ∧
      Flapjack.WordAlloc.wordStateEqRel popped targetPopped ∧
      (∀ live, Flapjack.WordAlloc.strongLocalsRel f live popped.locals targetPopped.locals) := by
  obtain ⟨popped', targetPopped, hpop, hpopT, hframe, -, hrelated⟩ :=
    returningPopCutRelation source target returned first second targetFirst
      targetSecond handler targetHandler targetStack f sourceRoots targetRoots sourcePerm
      targetPerm sameStack sourceRootRead targetRootRead rootMap firstRelated injective
      sourceKeys targetKeys stackValues
  rw [sourcePop] at hpop
  have hEq : popped = popped' := by simpa using hpop
  subst hEq
  exact ⟨targetPopped, hpopT, hframe, hrelated⟩

/-- The body transfer is not an oracle: a `PERM_STACK`-related target entry with
the same code makes the callee body work *equal*, by the checked permutation
driver.  This eliminates the previous `calleeWork` premise (its budget becomes
zero). -/
theorem calleeWork_permStack_zero {C F : Type}
    (prog : WordLangProgHOL (BitVec 64))
    (sourceEntry targetEntry : WordSemStateFiniteExact 64 C F)
    (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame 64))
    (href : targetEntry = { sourceEntry with permute := k, stack := xs })
    (hxs : List.Forall₂ permStack xs sourceEntry.stack)
    (hna : noAllocSubprogsHOL prog = true) (hni : noInstallSubprogsHOL prog = true)
    (hca : WordProps.noAllocCode sourceEntry.code)
    (hci : WordProps.noInstallCode sourceEntry.code) :
    wordPathWork prog targetEntry ≤ wordPathWork prog sourceEntry + 0 := by
  rw [href, wordPathWork_permStack_variant prog sourceEntry k xs hxs hna hni hca hci]
  omega

#print axioms calleeWork_permStack_zero

#print axioms ssaCallReturning_pop_alignment


theorem ssaBody_call_returning_no_body_oracle {C F : Type}
    (values : List Nat) (numset : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source target middle popped : WordSemStateFiniteExact 64 C F)
    (xs : List (WordLocW 64)) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (args1 args1T : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat)
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (ssa : Spt Nat) (na : Nat)
    (stackMov : WordLangProgHOL (BitVec 64)) (mapOut : Spt Nat) (counter : Nat)
    (regs : List Nat) (stackSet : WordLangCutsetsHOL)
    (movRetHandler : WordLangProgHOL (BitVec 64)) (convArgs : List Nat)
    (handlerT : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (refreshed prepared middleT targetPopped : WordSemStateFiniteExact 64 C F)
    (valuesT : List (WordLocW 64)) (moveArgs : WordLangProgHOL (BitVec 64))
    (envsT : Spt (WordLocW 64) × Spt (WordLocW 64))
    (locationT : WordLocW 64) (returnedT : List (WordLocW 64))
    (retBudget : Nat)
    (read : getVars args source = some xs)
    (bad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, numset, retCode, l1, l2)) xs) source.code
      source.stackSize = some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty numset.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs numset source.locals = some envs)
    (clock : source.clock ≠ 0)
    (run : fixClock (callEnv args1 ss (pushEnv envs none (decClock source)))
      (evaluate prog (callEnv args1 ss (pushEnv envs none (decClock source)))) =
      (some (.result location returned), middle))
    (pop : popEnv middle = some popped)
    (locEq : location = .loc l1 l2)
    (lenEq : returned.length = values.length)
    (domUnion : sptDomainEqUnion popped.locals envs.1 envs.2)
    (related : ssaLocalsRel na ssa source.locals target.locals)
    (allocated : isAllocVar na) (valid : ssaMapOK na ssa)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (produced : listNextVarRenameMove (width := 64) ssa (na + 2)
      ((sptToAList (sptUnion numset.1 numset.2)).map Prod.fst) = (stackMov, mapOut, counter))
    (convEq : convArgs = (List.range (args.map (optionLookup ssa)).length).map
      fun x => 2 * (x + 1))
    (stackSetEq : stackSet = Flapjack.WordAlloc.applyNummapsKey (optionLookup mapOut) numset)
    (moveEq : moveArgs = WordLangProgHOL.move 1 (convArgs.zip (args.map (optionLookup ssa))))
    (refEq : refreshed = (evaluate stackMov target).2)
    (prepEq : prepared = setVars convArgs xs refreshed)
    (valuesTEq : valuesT = xs)
    (findT : wordSemFindCode dest
      (wordSemAddRetLoc (some (regs, stackSet, movRetHandler, l1, l2)) valuesT)
      prepared.code prepared.stackSize = some (args1T, prog, ss))
    (domT : ¬ sptDomainEmpty stackSet.1) (nodupT : regs.Nodup)
    (cutT : wordSemCutEnvs stackSet prepared.locals = some envsT)
    (clockT : prepared.clock ≠ 0)
    (runT : fixClock (callEnv args1T ss (pushEnv envsT handlerT (decClock prepared)))
      (evaluate prog (callEnv args1T ss (pushEnv envsT handlerT (decClock prepared)))) =
      (some (.result locationT returnedT), middleT))
    (popT : popEnv middleT = some targetPopped)
    (locEqT : locationT = .loc l1 l2)
    (lenEqT : returnedT.length = regs.length)
    (domUnionT : sptDomainEqUnion targetPopped.locals envsT.1 envsT.2)
    (k : Nat → Nat → Nat) (stackXs : List (WordSemStackFrame 64))
    (href : callEnv args1T ss (pushEnv envsT handlerT (decClock prepared)) =
      { callEnv args1 ss (pushEnv envs none (decClock source)) with
        permute := k, stack := stackXs })
    (hxs : List.Forall₂ permStack stackXs
      (callEnv args1 ss (pushEnv envs none (decClock source))).stack)
    (hna : noAllocSubprogsHOL prog = true) (hni : noInstallSubprogsHOL prog = true)
    (hcaP : WordProps.noAllocCode
      (callEnv args1 ss (pushEnv envs none (decClock source))).code)
    (hciP : WordProps.noInstallCode
      (callEnv args1 ss (pushEnv envs none (decClock source))).code)
    (retWork : wordPathWork movRetHandler (setVars regs returnedT targetPopped) ≤
      wordPathWork retCode (setVars values returned popped) + retBudget) :
    wordPathWork (.seq stackMov
      (.seq moveArgs (.call (some (regs, stackSet, movRetHandler, l1, l2))
        dest convArgs handlerT))) target ≤
      wordPathWork (.call (some (values, numset, retCode, l1, l2)) dest args none) source +
        (retBudget + 4) := by
  have align := ssaCallReturning_prepare_alignment source target ssa na dest args xs numset
    envs.1 envs.2 stackMov mapOut counter (by simpa using cut) read related allocated valid
    frame bad produced
  dsimp only at align
  rw [← convEq, ← stackSetEq, ← moveEq, ← refEq, ← prepEq] at align
  obtain ⟨-, -, stackFixed, stackWork, argFixed, argWork, getT0, badT, -, -, -⟩ := align
  have getT : getVars convArgs prepared = some valuesT := by
    rw [valuesTEq]
    exact getT0
  have hclk : prepared.clock = refreshed.clock := by
    rw [prepEq]; rfl
  have htrm : prepared.termdep = refreshed.termdep := by
    rw [prepEq]; rfl
  have argFixedFix : fixClock refreshed (evaluate moveArgs refreshed) = (none, prepared) := by
    rw [argFixed]
    simp only [fixClock, if_neg (Nat.not_lt.mpr (Nat.le_of_eq hclk)), ← htrm]
    try rfl
  simpa using bodyWork_call_returning_result values numset retCode l1 l2 dest args none source
    middle popped xs envs args1 args1T prog ss location returned read bad find dom nodup cut
    clock run pop locEq lenEq domUnion regs stackSet movRetHandler convArgs handlerT target
    refreshed prepared middleT targetPopped valuesT stackMov moveArgs envsT locationT returnedT
    stackFixed stackWork argFixedFix argWork getT badT findT domT nodupT cutT clockT runT popT
    locEqT lenEqT domUnionT 0 retBudget
    (calleeWork_permStack_zero prog (callEnv args1 ss (pushEnv envs none (decClock source)))
      (callEnv args1T ss (pushEnv envsT handlerT (decClock prepared))) k stackXs href hxs hna
      hni hcaP hciP)
    retWork

#print axioms ssaBody_call_returning_no_body_oracle
#print axioms ssaBody_call_returning_executed_le

#print axioms ssaCcTrans_call_returning_none_output
#print axioms wordSemBadDestArgs_renameArgs
#print axioms wordPathWork_listNextVarRenameMove
#print axioms ssaCallReturning_prepare_alignment
#print axioms sourceCall_getVars_some_of_not_error
end InitECandidate.Runtime.FineCost
