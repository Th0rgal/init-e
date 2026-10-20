import InitECandidate.Runtime.PanWorkVector
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

noncomputable def expressionValue {F : Type} (s : PanSemStateFiniteExact 64 F)
    (e : ExpHOL 64) : Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e

/-- Initial exact expression rules. Variable copies use the flattened runtime
value size; expression entry is charged even when lookup fails. Recursive
expression constructors require explicit child rules and are not opaque leaves. -/
inductive ExpressionRun {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ExpHOL 64 → Option (ValueHOL 64) → List WorkEvent → Prop where
  | const (word : BitVec 64) :
      ExpressionRun s (.const word) (some (.val (.word word))) [.expression, .copy 1]
  | readVariable (kind : VarKind) (name) (value : ValueHOL 64)
      (lookup : expressionValue s (.var kind name) = some value) :
      ExpressionRun s (.var kind name) (some value)
        [.expression, .copy (flattenHOL value).length]
  | missingVariable (kind : VarKind) (name)
      (lookup : expressionValue s (.var kind name) = none) :
      ExpressionRun s (.var kind name) none [.expression]


  | compare (operator : Cmp) (left right : ExpHOL 64)
      (a b : BitVec 64) (leftEvents rightEvents : List WorkEvent)
      (lhs : ExpressionRun s left (some (.val (.word a))) leftEvents)
      (rhs : ExpressionRun s right (some (.val (.word b))) rightEvents) :
      ExpressionRun s (.cmp operator left right)
        (some (.val (.word (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL operator a b then 1 else 0))))
        (.expression :: (leftEvents ++ rightEvents ++ [.scalar 1]))
  | shift (operator : Shift) (left right : ExpHOL 64)
      (a b : BitVec 64) (leftEvents rightEvents : List WorkEvent)
      (lhs : ExpressionRun s left (some (.val (.word a))) leftEvents)
      (rhs : ExpressionRun s right (some (.val (.word b))) rightEvents) :
      ExpressionRun s (.shift operator left right)
        ((wordShiftHOL operator a b.toNat).map (fun word => .val (.word word)))
        (.expression :: (leftEvents ++ rightEvents ++ [.scalar 1]))

  | recordField (index : Nat) (record : ExpHOL 64) (values : List (ValueHOL 64))
      (events : List WorkEvent)
      (child : ExpressionRun s record (some (.rStruct values)) events) :
      ExpressionRun s (.rfield index record) values[index]?
        (.expression :: (events ++ [.copy (((values[index]?).map
          (fun value => (flattenHOL value).length)).getD 0)]))

  | loadByte (addressExp : ExpHOL 64) (address : BitVec 64)
      (events : List WorkEvent)
      (child : ExpressionRun s addressExp (some (.val (.word address))) events) :
      ExpressionRun s (.loadByte addressExp)
        (expressionValue s (.loadByte (.const address)))
        (.expression :: (events ++ [.memory 1]))
  | load32 (addressExp : ExpHOL 64) (address : BitVec 64)
      (events : List WorkEvent)
      (child : ExpressionRun s addressExp (some (.val (.word address))) events) :
      ExpressionRun s (.load32 addressExp)
        (expressionValue s (.load32 (.const address)))
        (.expression :: (events ++ [.memory 1]))
  | loadByteAddressFailure (addressExp : ExpHOL 64) (events : List WorkEvent)
      (child : ExpressionRun s addressExp none events) :
      ExpressionRun s (.loadByte addressExp) none (.expression :: events)
  | load32AddressFailure (addressExp : ExpHOL 64) (events : List WorkEvent)
      (child : ExpressionRun s addressExp none events) :
      ExpressionRun s (.load32 addressExp) none (.expression :: events)

  | binaryOp (operator : BinOp) (left right : ExpHOL 64)
      (a b : BitVec 64) (leftEvents rightEvents : List WorkEvent)
      (lhs : ExpressionRun s left (some (.val (.word a))) leftEvents)
      (rhs : ExpressionRun s right (some (.val (.word b))) rightEvents) :
      ExpressionRun s (.op operator [left, right])
        ((wordOpHOL operator [a, b]).map (fun word => .val (.word word)))
        (.expression :: (leftEvents ++ rightEvents ++ [.scalar 1]))

  | baseAddress : ExpressionRun s .baseAddr (some (.val (.word s.baseAddr)))
      [.expression, .copy 1]
  | topAddress : ExpressionRun s .topAddr (some (.val (.word s.topAddr)))
      [.expression, .copy 1]
  | wordBytes : ExpressionRun s .bytesInWord (some (.val (.word (bytesInWordHOL 64))))
      [.expression, .copy 1]

theorem ExpressionRun.sound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {value : Option (ValueHOL 64)} {events : List WorkEvent}
    (run : ExpressionRun s e value events) : expressionValue s e = value := by
  induction run with
  | const word => rfl
  | readVariable kind name value lookup => exact lookup
  | missingVariable kind name lookup => exact lookup
  | compare operator left right a b leftEvents rightEvents lhs rhs ihLeft ihRight =>
    simp only [expressionValue] at ihLeft ihRight ⊢
    simp only [evalHOLExact, ihLeft, ihRight]
  | shift operator left right a b leftEvents rightEvents lhs rhs ihLeft ihRight =>
    simp only [expressionValue] at ihLeft ihRight ⊢
    simp only [evalHOLExact, ihLeft, ihRight]
  | recordField index record values events child ih =>
    simp only [expressionValue] at ih ⊢
    simp only [evalHOLExact, ih]
  | loadByte addressExp address events child ih =>
    simp only [expressionValue] at ih ⊢
    simp only [evalHOLExact, ih]
  | load32 addressExp address events child ih =>
    simp only [expressionValue] at ih ⊢
    simp only [evalHOLExact, ih]
  | loadByteAddressFailure addressExp events child ih =>
    simp only [expressionValue] at ih ⊢
    simp only [evalHOLExact, ih]
  | load32AddressFailure addressExp events child ih =>
    simp only [expressionValue] at ih ⊢
    simp only [evalHOLExact, ih]
  | binaryOp operator left right a b leftEvents rightEvents lhs rhs ihLeft ihRight =>
    simp only [expressionValue] at ihLeft ihRight ⊢
    simp [evalHOLExact, evalListHOLExact, ihLeft, ihRight, valueIsWord, valueWord]
  | baseAddress => rfl
  | topAddress => rfl
  | wordBytes => rfl

theorem variable_work_score (coeff : Work) (value : ValueHOL 64) :
    coeff.score (executionWork [.expression, .copy (flattenHOL value).length]) =
      coeff.expressions + coeff.movedWords * (flattenHOL value).length := by
  simp [executionWork, WorkEvent.units, Work.plus, Work.score]

#print axioms ExpressionRun.sound
#print axioms variable_work_score
end InitECandidate.Runtime.FineCost
