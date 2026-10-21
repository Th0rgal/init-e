import InitECandidate.Runtime.FullSSAQuantitativeCost
import InitECandidate.Runtime.WordArityCodeMap
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 3000000

/-- Whole function table with full SSA setup using each entry's actual arity. -/
def fullSSACodeTable (code : Spt (Nat × WordLangProgHOL (BitVec 64))) :
    Spt (Nat × WordLangProgHOL (BitVec 64)) := wordArityCodeMap fullSsaCcTrans code

theorem fullSSACodeTable_lookup (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (label : Nat) :
    sptLookup label (fullSSACodeTable code) =
      (sptLookup label code).map (fun entry => (entry.1,fullSsaCcTrans entry.1 entry.2)) :=
  wordArityCodeMap_lookup _ _ _

theorem fullSSACodeTable_mem (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (label : Nat) :
    sptMem label (fullSSACodeTable code) = sptMem label code := by
  apply propext
  rw [sptMem_iff_lookup,sptMem_iff_lookup,fullSSACodeTable_lookup]
  cases sptLookup label code <;> simp

theorem fullSSACodeTable_findCode (destination : Option Nat) (arguments : List (WordLocW 64))
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (sizes : Spt Nat) :
    wordSemFindCode destination arguments (fullSSACodeTable code) sizes =
      (wordSemFindCode destination arguments code sizes).map
        (fun found => (found.1,fullSsaCcTrans found.1.length found.2.1,found.2.2)) :=
  wordArityCodeMap_findCode _ _ _ _ _

/-- Original SSA frame, except that the target code field contains the actual
mapped function table. Both the remaining frame and the code equation are
required; this does not silently equate original and compiled callees. -/
def FullSSATableFrame {C F : Type} (source target : WordSemStateFiniteExact 64 C F) : Prop :=
  Flapjack.WordAlloc.wordStateEqRel source {target with code := source.code} ∧
    target.code = fullSSACodeTable source.code

theorem fullSSATableFrame_initial {C F : Type} (source : WordSemStateFiniteExact 64 C F) :
    FullSSATableFrame source {source with code := fullSSACodeTable source.code} := by
  simp [FullSSATableFrame,Flapjack.WordAlloc.wordStateEqRel]

theorem fullSSATableFrame_clock {C F : Type} (source target : WordSemStateFiniteExact 64 C F)
    (frame : FullSSATableFrame source target) : source.clock = target.clock ∧ source.termdep = target.termdep := by
  have related := frame.1
  simp only [Flapjack.WordAlloc.wordStateEqRel] at related
  tauto


/-- Entering a callee replaces locals and localsSize, so a mapped SSA frame
becomes exact equality apart from the caller's scheduler and code fields. -/
theorem fullSSATableFrame_callEnv {C F : Type}
    (source target : WordSemStateFiniteExact 64 C F) (frame : FullSSATableFrame source target)
    (arguments : List (WordLocW 64)) (size : Option Nat) :
    callEnv arguments size target =
      {callEnv arguments size source with code := fullSSACodeTable source.code, permute := target.permute} := by
  cases source
  cases target
  simp_all [FullSSATableFrame,Flapjack.WordAlloc.wordStateEqRel,WordSemStateFiniteExact.callEnv]

theorem fullSSATableFrame_decClock {C F : Type}
    (source target : WordSemStateFiniteExact 64 C F) (frame : FullSSATableFrame source target) :
    FullSSATableFrame (decClock source) (decClock target) := by
  simp_all [FullSSATableFrame,Flapjack.WordAlloc.wordStateEqRel,decClock]

theorem fullSSATableFrame_flush {C F : Type}
    (source target : WordSemStateFiniteExact 64 C F) (frame : FullSSATableFrame source target) :
    FullSSATableFrame (flushState true source) (flushState true target) := by
  simp_all [FullSSATableFrame,Flapjack.WordAlloc.wordStateEqRel,flushState]

#print axioms fullSSATableFrame_callEnv
#print axioms fullSSATableFrame_decClock
#print axioms fullSSATableFrame_flush

#print axioms fullSSACodeTable_findCode
#print axioms fullSSACodeTable_mem
#print axioms fullSSATableFrame_initial
#print axioms fullSSATableFrame_clock
end InitECandidate.Runtime.FineCost
