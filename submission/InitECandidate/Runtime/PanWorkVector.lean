import InitECandidate.Runtime.PanExecutionWork

namespace InitECandidate.Runtime.FineCost

/-- Semantic work units. The compiler certificate supplies coefficients;
these counters do not assume that one source operation is one native step. -/
structure Work where
  statements : Nat := 0
  expressions : Nat := 0
  scalarOps : Nat := 0
  memoryAccesses : Nat := 0
  movedWords : Nat := 0
  frameSlots : Nat := 0
  transferBytes : Nat := 0
  primitiveBlocks : Nat := 0
  nativeEvents : Nat := 0
  deriving DecidableEq, Repr

def Work.plus (a b : Work) : Work :=
  ⟨a.statements+b.statements, a.expressions+b.expressions,
   a.scalarOps+b.scalarOps, a.memoryAccesses+b.memoryAccesses,
   a.movedWords+b.movedWords, a.frameSlots+b.frameSlots,
   a.transferBytes+b.transferBytes, a.primitiveBlocks+b.primitiveBlocks,
   a.nativeEvents+b.nativeEvents⟩

/-- A separate coefficient for each implementation cost avoids multiplying
unrelated worst-case bounds across the compiler pipeline. -/
def Work.score (coeff work : Work) : Nat :=
  coeff.statements*work.statements + coeff.expressions*work.expressions +
  coeff.scalarOps*work.scalarOps + coeff.memoryAccesses*work.memoryAccesses +
  coeff.movedWords*work.movedWords + coeff.frameSlots*work.frameSlots +
  coeff.transferBytes*work.transferBytes + coeff.primitiveBlocks*work.primitiveBlocks +
  coeff.nativeEvents*work.nativeEvents

inductive WorkEvent where
  | statement
  | expression
  | scalar (operations : Nat)
  | memory (accesses : Nat)
  | copy (words : Nat)
  | frame (slots : Nat)
  | transfer (bytes : Nat)
  | primitive (blocks : Nat)
  | nativeEvent
  deriving DecidableEq, Repr

def WorkEvent.units : WorkEvent → Work
  | .statement => { statements := 1 }
  | .expression => { expressions := 1 }
  | .scalar n => { scalarOps := n }
  | .memory n => { memoryAccesses := n }
  | .copy n => { movedWords := n }
  | .frame n => { frameSlots := n }
  | .transfer n => { transferBytes := n }
  | .primitive n => { primitiveBlocks := n }
  | .nativeEvent => { nativeEvents := 1 }

def executionWork : List WorkEvent → Work
  | [] => {}
  | event :: rest => event.units.plus (executionWork rest)

theorem Work.score_plus (coeff left right : Work) :
    coeff.score (left.plus right) = coeff.score left + coeff.score right := by
  simp only [Work.score, Work.plus, Nat.mul_add]
  omega

theorem Work.plus_assoc (a b c : Work) :
    (a.plus b).plus c = a.plus (b.plus c) := by
  cases a; cases b; cases c
  simp only [Work.plus, Nat.add_assoc]

theorem executionWork_append (left right : List WorkEvent) :
    executionWork (left ++ right) = (executionWork left).plus (executionWork right) := by
  induction left with
  | nil => simp [executionWork, Work.plus]
  | cons event rest ih =>
    simp only [List.cons_append, executionWork, ih, Work.plus_assoc]

/-- Each variable-size event has an exactly linear score in its recorded size.
Semantic trace rules must establish that size from the actual operation. -/
theorem transfer_score (coeff : Work) (bytes : Nat) :
    coeff.score (WorkEvent.transfer bytes).units = coeff.transferBytes * bytes := by
  simp [Work.score, WorkEvent.units]

theorem primitive_score (coeff : Work) (blocks : Nat) :
    coeff.score (WorkEvent.primitive blocks).units = coeff.primitiveBlocks * blocks := by
  simp [Work.score, WorkEvent.units]

#print axioms Work.score_plus
#print axioms executionWork_append
#print axioms transfer_score
#print axioms primitive_score
end InitECandidate.Runtime.FineCost
