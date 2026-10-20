import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Only nonrecursive semantic clauses are admitted as opaque leaves. Calls,
loops, declarations and control composition must have their own trace rules. -/
def atomic : ProgHOL 64→Bool
 | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .store32 _ _ | .storeByte _ _ => true
 | .break | .continue | .raise _ _ | .return _ | .shMemLoad _ _ _ _ | .shMemStore _ _ _ => true
 | .extCall _ _ _ _ _ | .tick | .annot _ _ => true
 | _=>false

/-- An executed source-node trace, indexed by the authoritative finite HOL
semantics. It records only visited branches and stops at terminal outcomes.
Local weights are supplied separately by compiler-cost proofs. Initial rules
cover atoms, sequences and conditionals; recursive clauses are intentionally
not hidden behind an unrestricted evaluator leaf. -/
inductive TraceRun {F : Type} : PanSemStateFiniteExact 64 F→ProgHOL 64→
 Option (PanSemResultExact 64)→PanSemStateFiniteExact 64 F→List (ProgHOL 64)→Prop where
 | atom {s p r post} (supported : atomic p=true)
   (run : evaluateHOLFiniteState s p=(r,post)) : TraceRun s p r post [p]
 | seqNext {s first middle second r post left right}
   (one : TraceRun s first none middle left) (two : TraceRun middle second r post right) :
   TraceRun s (.seq first second) r post (.seq first second::(left++right))
 | seqStop {s first second r post left} (terminal : r≠none)
   (one : TraceRun s first r post left) :
   TraceRun s (.seq first second) r post (.seq first second::left)
 | iteYes {s condition yes no value r post trace}
   (guard : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) condition=
    some (.val (.word value))) (nonzero : value≠0)
   (body : TraceRun s yes r post trace) :
   TraceRun s (.ite condition yes no) r post (.ite condition yes no::trace)
 | iteNo {s condition yes no r post trace}
   (guard : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) condition=
    some (.val (.word 0))) (body : TraceRun s no r post trace) :
   TraceRun s (.ite condition yes no) r post (.ite condition yes no::trace)

theorem TraceRun.sound {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {p : ProgHOL 64} {r : Option (PanSemResultExact 64)} {trace : List (ProgHOL 64)}
 (run : TraceRun s p r post trace) : evaluateHOLFiniteState s p=(r,post) := by
 induction run with
 | atom supported run=>exact run
 | seqNext one two ihOne ihTwo=>
   rw [evaluateHOLFiniteState_seq]
   dsimp only
   rw [fixClockHOLFinite_evaluateState,ihOne]
   exact ihTwo
 | @seqStop state first second result final left terminal one ih=>
   rw [evaluateHOLFiniteState_seq]
   dsimp only
   rw [fixClockHOLFinite_evaluateState,ih]
   cases result <;>simp_all
 | @iteYes state condition yes no value result final trace guard nonzero body ih=>
   rw [evaluateHOLFiniteState_ite,guard]
   have zero : value≠(0#64):=nonzero
   simpa [zero] using ih
 | iteNo guard body ih=>
   rw [evaluateHOLFiniteState_ite,guard]
   simpa using ih

/-- A node's local weight can charge expression operations, structured words,
register spills and native expansion once those local bounds are certified. -/
def traceWork (weight : ProgHOL 64→Nat) (trace : List (ProgHOL 64)) : Nat :=
 (trace.map weight).sum

theorem traceWork_append (weight : ProgHOL 64→Nat) (left right : List (ProgHOL 64)) :
 traceWork weight (left++right)=traceWork weight left+traceWork weight right := by
 simp [traceWork]

/-- Composition adds visited work instead of multiplying global maxima. -/
theorem traceWork_sequence (weight : ProgHOL 64→Nat) (first second : ProgHOL 64)
 (left right : List (ProgHOL 64)) :
 traceWork weight (.seq first second::(left++right))=
 weight (.seq first second)+traceWork weight left+traceWork weight right := by
 simp [traceWork,Nat.add_assoc]

#print axioms TraceRun.sound
#print axioms traceWork_sequence
end InitECandidate.Runtime.FineCost
