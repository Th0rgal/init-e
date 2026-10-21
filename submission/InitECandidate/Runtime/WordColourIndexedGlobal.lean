import InitECandidate.Runtime.WordColourIndexedReturn
import InitECandidate.Runtime.WordColourAlloc

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordAlloc Flapjack.RegAlloc
open Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordAlloc.Proofs (evenStartingLocals)
set_option maxHeartbeats 4000000

/-!
# Whole-table function-indexed register colouring

Per-function facts certified for the actual allocated table: each source
function's own colouring is accepted by the clash-tree check (so
`colouringOk` holds), fixes the physical registers, and the body installs no
code. With these, every function's coloured body over the allocated table
pays at most its source body's function-indexed work, with coefficient one.
-/

/-- Per-function certificates for an allocated table. -/
def ColourTableFacts (source : Spt (Nat × WordLangProgHOL (BitVec 64))) (col : Nat → Nat → Nat) : Prop :=
  ∀ label arity body, sptLookup label source = some (arity, body) →
    colouringOk (col label) body .ln [] ∧ (∀ n, isPhyVar n = true → col label n = n) ∧
      noInstallSubprogsHOL body = true

/-- Structural recursion over one function body. -/
theorem colourIndexedGoal_all {C F : Type} (TP : WordLangProgHOL (BitVec 64) → Nat)
    (SP : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (source target : Spt (Nat × WordLangProgHOL (BitVec 64))) (col : Nat → Nat → Nat)
    (function : Nat) (f : Nat → Nat) (table : ColourAllocTable source target col)
    (sourceFree : WordProps.noInstallCode source) (targetFree : WordProps.noInstallCode target)
    (sameDomain : ∀ label, sptMem label target = sptMem label source)
    (leafPrice : ∀ p, TP (applyColour f p) ≤ SP function p)
    (permuteCost : IndexedPermuteCost C F SP) :
    ∀ prog : WordLangProgHOL (BitVec 64), ColourIndexedGoal C F TP SP source target col function f prog
  | .seq c1 c2 => colourIndexed_seq TP SP source target col function f sourceFree targetFree leafPrice
      permuteCost c1 c2
      (colourIndexedGoal_all TP SP source target col function f table sourceFree targetFree sameDomain
        leafPrice permuteCost c1)
      (colourIndexedGoal_all TP SP source target col function f table sourceFree targetFree sameDomain
        leafPrice permuteCost c2)
  | .ite cmp r ri c1 c2 => colourIndexed_ite TP SP source target col function f leafPrice cmp r ri c1 c2
      (colourIndexedGoal_all TP SP source target col function f table sourceFree targetFree sameDomain
        leafPrice permuteCost c1)
      (colourIndexedGoal_all TP SP source target col function f table sourceFree targetFree sameDomain
        leafPrice permuteCost c2)
  | .mustTerminate body => colourIndexed_mustTerminate TP SP source target col function f leafPrice body
      (colourIndexedGoal_all TP SP source target col function f table sourceFree targetFree sameDomain
        leafPrice permuteCost body)
  | .loop names body exitNames => colourIndexed_loop TP SP source target col function f sourceFree
      targetFree leafPrice permuteCost names exitNames body
      (colourIndexedGoal_all TP SP source target col function f table sourceFree targetFree sameDomain
        leafPrice permuteCost body)
  | .call none dest args handler => colourIndexed_tail TP SP source target col function f table leafPrice
      dest args handler
  | .call (some (n, (n1, n2), rh, l1, l2)) dest args none =>
      colourIndexed_returning TP SP source target col function f table sourceFree targetFree leafPrice
        permuteCost n n1 n2 rh l1 l2 dest args none
        (colourIndexedGoal_all TP SP source target col function f table sourceFree targetFree sameDomain
          leafPrice permuteCost rh)
        (fun _ _ _ _ h => nomatch h)
  | .call (some (n, (n1, n2), rh, l1, l2)) dest args (some (v, hp, l1', l2')) =>
      colourIndexed_returning TP SP source target col function f table sourceFree targetFree leafPrice
        permuteCost n n1 n2 rh l1 l2 dest args (some (v, hp, l1', l2'))
        (colourIndexedGoal_all TP SP source target col function f table sourceFree targetFree sameDomain
          leafPrice permuteCost rh)
        (fun _ _ _ _ h => by
          cases h
          exact colourIndexedGoal_all TP SP source target col function f table sourceFree targetFree
            sameDomain leafPrice permuteCost hp)
  | .skip => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain leafPrice _ rfl
      (applyColourGoal_all _)
  | .move pri moves => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain
      leafPrice _ rfl (applyColourGoal_all (.move pri moves))
  | .inst i => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain leafPrice _ rfl
      (applyColourGoal_all (.inst i))
  | .assign v e => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain leafPrice _
      rfl (applyColourGoal_all (.assign v e))
  | .get v name => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain leafPrice _
      rfl (applyColourGoal_all (.get v name))
  | .set name e => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain leafPrice _
      rfl (applyColourGoal_all (.set name e))
  | .store e v => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain leafPrice _
      rfl (applyColourGoal_all (.store e v))
  | .alloc n names => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain
      leafPrice _ rfl (applyColourGoal_all (.alloc n names))
  | .storeConsts a b c d ws => colourIndexed_atomic TP SP source target col function f sourceFree
      sameDomain leafPrice _ rfl (applyColourGoal_all (.storeConsts a b c d ws))
  | .raise n => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain leafPrice _
      rfl (applyColourGoal_all (.raise n))
  | .return n ms => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain leafPrice
      _ rfl (applyColourGoal_all (.return n ms))
  | .break k => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain leafPrice _
      rfl (applyColourGoal_all (.break k))
  | .continue k => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain leafPrice
      _ rfl (applyColourGoal_all (.continue k))
  | .tick => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain leafPrice _ rfl
      (applyColourGoal_all .tick)
  | .opCurrHeap b dst src => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain
      leafPrice _ rfl (applyColourGoal_all (.opCurrHeap b dst src))
  | .locValue r l1 => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain
      leafPrice _ rfl (applyColourGoal_all (.locValue r l1))
  | .install ptr len dptr dlen names => colourIndexed_atomic TP SP source target col function f sourceFree
      sameDomain leafPrice _ rfl (applyColourGoal_all (.install ptr len dptr dlen names))
  | .codeBufferWrite r1 r2 => colourIndexed_atomic TP SP source target col function f sourceFree
      sameDomain leafPrice _ rfl (applyColourGoal_all (.codeBufferWrite r1 r2))
  | .dataBufferWrite r1 r2 => colourIndexed_atomic TP SP source target col function f sourceFree
      sameDomain leafPrice _ rfl (applyColourGoal_all (.dataBufferWrite r1 r2))
  | .ffi fi p1 l1 p2 l2 names => colourIndexed_atomic TP SP source target col function f sourceFree
      sameDomain leafPrice _ rfl (applyColourGoal_all (.ffi fi p1 l1 p2 l2 names))
  | .shareInst op v e => colourIndexed_atomic TP SP source target col function f sourceFree sameDomain
      leafPrice _ rfl (applyColourGoal_all (.shareInst op v e))

theorem ColourAllocTable.sameDomain {source target : Spt (Nat × WordLangProgHOL (BitVec 64))}
    {col : Nat → Nat → Nat} (table : ColourAllocTable source target col) (label : Nat) :
    sptMem label target = sptMem label source := by
  apply propext
  rw [sptMem_iff_lookup, sptMem_iff_lookup]
  rcases found : sptLookup label source with _ | ⟨arity, body⟩
  · rw [(table label).1 found]
  · rw [(table label).2 arity body found]
    simp

/-- Every guarded callee summary holds: well-founded induction on
termination depth and clock. -/
theorem colourCalleeIH_all {C F : Type} (TP : WordLangProgHOL (BitVec 64) → Nat)
    (SP : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (source target : Spt (Nat × WordLangProgHOL (BitVec 64))) (col : Nat → Nat → Nat)
    (table : ColourAllocTable source target col) (facts : ColourTableFacts source col)
    (sourceFree : WordProps.noInstallCode source) (targetFree : WordProps.noInstallCode target)
    (leafPrice : ∀ label p, TP (applyColour (col label) p) ≤ SP label p)
    (permuteCost : IndexedPermuteCost C F SP) :
    ∀ depth clock, ColourCalleeIH C F TP SP source target col depth clock := by
  intro depth
  induction depth using Nat.strong_induction_on with
  | _ depth outer =>
    intro clock
    induction clock using Nat.strong_induction_on with
    | _ clock inner =>
      intro label arity body entry targetPermute smaller lookup entryCode even
      obtain ⟨ok, physical, bodyFree⟩ := facts label arity body lookup
      have entryIH : ColourCalleeIH C F TP SP source target col entry.termdep entry.clock := by
        simp only [Prod.lex_def] at smaller
        rcases smaller with lower | ⟨same, earlier⟩
        · exact outer entry.termdep lower entry.clock
        · rw [same]; exact inner entry.clock earlier
      apply colourIndexedGoal_all TP SP source target col label (col label) table sourceFree targetFree
        table.sameDomain (leafPrice label) permuteCost body entry
        {entry with code := target, permute := targetPermute} .ln [] entryIH bodyFree entryCode rfl
      refine ⟨ok, ?_, strongLocals_self (col label) entry.locals _ even physical⟩
      simp [wordStateEqRel]

/-- Whole-table theorem: a function body coloured by its own colouring and run
over the allocated table, from any physical-register entry over the source
table, has the source's result, frame and terminal locals, and at most the
source's function-indexed work, under one source scheduler. -/
theorem colourIndexed_table {C F : Type} (TP : WordLangProgHOL (BitVec 64) → Nat)
    (SP : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (source target : Spt (Nat × WordLangProgHOL (BitVec 64))) (col : Nat → Nat → Nat)
    (table : ColourAllocTable source target col) (facts : ColourTableFacts source col)
    (sourceFree : WordProps.noInstallCode source) (targetFree : WordProps.noInstallCode target)
    (leafPrice : ∀ label p, TP (applyColour (col label) p) ≤ SP label p)
    (label arity : Nat) (body : WordLangProgHOL (BitVec 64)) (lookup : sptLookup label source = some (arity, body))
    (entry : WordSemStateFiniteExact 64 C F) (entryCode : entry.code = source)
    (even : evenStartingLocals entry.locals) :
    ColourIndexedPost TP SP label (col label) body .ln [] entry {entry with code := target} :=
  colourCalleeIH_all TP SP source target col table facts sourceFree targetFree leafPrice
    (indexedPermuteCost C F SP) entry.termdep (entry.clock + 1) label arity body entry entry.permute
    (Prod.Lex.right _ (Nat.lt_succ_self _)) lookup entryCode even

/-- Ghost-price instance: the source pays each function's body exactly at its
final coloured price. The leaf premise holds with equality, so the only
remaining inputs are the table certificates. -/
theorem colourIndexed_table_ghost {C F : Type} (TP : WordLangProgHOL (BitVec 64) → Nat)
    (source target : Spt (Nat × WordLangProgHOL (BitVec 64))) (col : Nat → Nat → Nat)
    (table : ColourAllocTable source target col) (facts : ColourTableFacts source col)
    (sourceFree : WordProps.noInstallCode source) (targetFree : WordProps.noInstallCode target)
    (label arity : Nat) (body : WordLangProgHOL (BitVec 64)) (lookup : sptLookup label source = some (arity, body))
    (entry : WordSemStateFiniteExact 64 C F) (entryCode : entry.code = source)
    (even : evenStartingLocals entry.locals) :
    ColourIndexedPost TP (fun l p => TP (applyColour (col l) p)) label (col label) body .ln [] entry
      {entry with code := target} :=
  colourIndexed_table TP (fun l p => TP (applyColour (col l) p)) source target col table facts sourceFree
    targetFree (fun _ _ => Nat.le_refl _) label arity body lookup entry entryCode even

/-- Per-function certificates from the production oracle check. -/
theorem colourTableEntry_of_oracle (c : Compiler.Encoders.Asm.AsmConfigExact 64) (k : Nat)
    (prog coloured : WordLangProgHOL (BitVec 64)) (colour : Spt Nat) (hwf : wfCutsets prog)
    (free : noInstallSubprogsHOL prog = true)
    (hor : oracleColourOk k (some colour) (getClashTree prog []) prog (getForced c prog []) = some coloured) :
    coloured = applyColour (totalColour colour) prog ∧ colouringOk (totalColour colour) prog .ln [] ∧
      (∀ n, isPhyVar n = true → totalColour colour n = n) ∧ noInstallSubprogsHOL prog = true := by
  have hln : ∀ x, ¬ sptDomain (.ln : NumSet) x := fun x h => by
    simp [sptDomain, sptLookup] at h
  have hlnimg : sptDomain (.ln : NumSet) =
      (fun y => ∃ x, sptDomain (.ln : NumSet) x ∧ totalColour colour x = y) := by
    funext y
    apply propext
    exact ⟨fun h => absurd h (hln y), fun ⟨x, hx, _⟩ => absurd hx (hln x)⟩
  simp only [oracleColourOk] at hor
  split at hor
  · next h1 =>
    split at hor
    · simp only [Option.some.injEq] at hor
      simp only [Bool.and_eq_true] at h1
      obtain ⟨hev, hcc⟩ := h1
      obtain ⟨⟨livein, flivein⟩, hcc⟩ := Option.isSome_iff_exists.mp hcc
      have hevc : ∀ x v, sptLookup x colour = some v → isPhyVar x = true → 2 * v = x :=
        fun x v hl hp => by
          have hm := (sptMemToAList colour x v).mpr hl
          have := List.all_eq_true.mp hev (x, v) hm
          simp only [hp, ↓reduceIte, beq_iff_eq] at this
          simp only [isPhyVar, decide_eq_true_eq] at hp
          omega
      have hco := (clashTreeColouringOk prog [] (totalColour colour) .ln .ln livein flivein
        ⟨hwf, rfl, (fun _ h => by cases h), hlnimg, (fun a _ ha => absurd ha (hln a)), hcc⟩).2.2.1
      exact ⟨hor.symm, hco, totalColour_phys colour hevc, free⟩
    · cases hor
  · cases hor

#print axioms colourIndexedGoal_all
#print axioms colourCalleeIH_all
#print axioms colourIndexed_table
#print axioms colourIndexed_table_ghost
#print axioms colourTableEntry_of_oracle
end InitECandidate.Runtime.FineCost
