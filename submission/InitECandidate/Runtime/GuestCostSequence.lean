import InitECandidate.Runtime.GuestCostWorkScore
import InitECandidate.Runtime.PanStatementWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

variable {F : Type}

/-- Price additivity for a sequence: a straight-line prefix and its suffix each
keep their traced events and their prices add. The structural `seq` node emits
no event of its own, so association never changes cost. -/
theorem seq_statement_cost (coeff : Work) {s middle post : PanSemStateFiniteExact 64 F}
    {first second : ProgHOL 64} {r : Option (PanSemResultExact 64)}
    {left right : List WorkEvent} (A B : Nat)
    (one : StatementRun s first none middle left) (two : StatementRun middle second r post right)
    (oneCost : coeff.score (executionWork left) ≤ A)
    (twoCost : coeff.score (executionWork right) ≤ B) :
    StatementRun s (.seq first second) r post (left ++ right) ∧
    coeff.score (executionWork (left ++ right)) ≤ A + B := by
  refine ⟨StatementRun.seqNext one two, ?_⟩
  rw [executionWork_score_append]
  omega

/-- Price additivity for a taken conditional branch. -/
theorem ite_statement_cost (coeff : Work) {s post : PanSemStateFiniteExact 64 F}
    {condition : ExpHOL 64} {yes no : ProgHOL 64} {r : Option (PanSemResultExact 64)}
    {value : BitVec 64} {guardEvents bodyEvents : List WorkEvent} (G B : Nat)
    (guard : CostedExpressionRun s condition (some (.val (.word value))) guardEvents)
    (nonzero : value ≠ 0) (body : StatementRun s yes r post bodyEvents)
    (guardCost : coeff.score (executionWork (.statement :: guardEvents)) ≤ G)
    (bodyCost : coeff.score (executionWork bodyEvents) ≤ B) :
    StatementRun s (.ite condition yes no) r post (.statement :: (guardEvents ++ bodyEvents)) ∧
    coeff.score (executionWork (.statement :: (guardEvents ++ bodyEvents))) ≤ G + B := by
  refine ⟨StatementRun.iteYes guard nonzero body, ?_⟩
  rw [executionWork_score_cons, executionWork_score_append]
  have splitGuard := executionWork_score_cons coeff .statement guardEvents
  omega

/-- Price additivity for a word store statement. -/
theorem store_statement_cost (coeff : Work) {s : PanSemStateFiniteExact 64 F}
    {destination source : ExpHOL 64} {address value : BitVec 64}
    {stored : ValueHOL 64}
    {memory : RiscV.Word 64 → HolWordLab 64} {addressEvents valueEvents : List WorkEvent}
    (D S : Nat)
    (dst : CostedExpressionRun s destination (some (.val (.word address))) addressEvents)
    (src : CostedExpressionRun s source (some stored) valueEvents)
    (write : @panMemStoresHOL 64 _ address (flattenHOL stored) s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.memory = some memory)
    (dstCost : coeff.score (executionWork addressEvents) ≤ D)
    (srcCost : coeff.score (executionWork valueEvents) ≤ S) :
    StatementRun s (.store destination source) none { s with memory := memory }
      (.statement :: (addressEvents ++ valueEvents ++ [.memory (flattenHOL stored).length])) ∧
    coeff.score (executionWork
        (.statement :: (addressEvents ++ valueEvents ++ [.memory (flattenHOL stored).length]))) ≤
      coeff.statements + D + S + coeff.memoryAccesses * (flattenHOL stored).length := by
  refine ⟨StatementRun.storeValue dst src write, ?_⟩
  rw [executionWork_score_cons, score_statement]
  rw [executionWork_score_append, executionWork_score_append]
  rw [score_singleton, guest_score_memory]
  omega

/-- Price additivity for a declared local: the initialiser, the frame slot, the
traced body and the restored previous value. -/
theorem dec_statement_cost (coeff : Work) {s post : PanSemStateFiniteExact 64 F}
    {name : MlStringHOL} {shape : ShapeHOL} {initializer : ExpHOL 64} {body : ProgHOL 64}
    {value : ValueHOL 64} {initEvents bodyEvents : List WorkEvent}
    {r : Option (PanSemResultExact 64)} (I B : Nat)
    (init : CostedExpressionRun s initializer (some value) initEvents)
    (shapeMatch : shapeEqHOL shape (shapeOfHOLExact value) = true)
    (bodyRun : StatementRun (setVarHOLFinite name value s) body r post bodyEvents)
    (initCost : coeff.score (executionWork initEvents) ≤ I)
    (bodyCost : coeff.score (executionWork bodyEvents) ≤ B) :
    coeff.score (executionWork
        (.statement :: (initEvents ++ [.copy (flattenHOL value).length, .frame 1] ++
          bodyEvents ++ [.copy (((s.locals.lookup name).map
            (fun previous => (flattenHOL previous).length)).getD 0)]))) ≤
      coeff.statements + I + coeff.movedWords * (flattenHOL value).length + coeff.frameSlots +
        B + coeff.movedWords * (((s.locals.lookup name).map
          (fun previous => (flattenHOL previous).length)).getD 0) := by
  rw [executionWork_score_cons, score_statement]
  rw [executionWork_score_append, executionWork_score_append, executionWork_score_append]
  rw [score_pair, guest_score_copy, score_frame, score_singleton, guest_score_copy]
  omega

#print axioms seq_statement_cost
#print axioms ite_statement_cost
#print axioms store_statement_cost
#print axioms dec_statement_cost
end InitECandidate.Runtime.FineCost
