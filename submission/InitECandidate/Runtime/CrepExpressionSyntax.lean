import InitECandidate.Runtime.CrepExpressionBudget
namespace InitECandidate.Runtime
open Flapjack

/- Static expression overhead counts generated comparisons; arithmetic and
loads themselves introduce no Loop clock ticks. -/
mutual
  def crepExprFuel {width : Nat} [NeZero width] : CrepExpHOL width → Nat
    | .load e | .loadByte e | .load32 e => crepExprFuel e
    | .op _ es | .crepOp _ es => crepExpsFuel es
    | .cmp _ a b => crepExprFuel a + crepExprFuel b + 1
    | .shift _ a b => crepExprFuel a + crepExprFuel b
    | _ => 0
  termination_by e => sizeOf e
  def crepExpsFuel {width : Nat} [NeZero width] : List (CrepExpHOL width) → Nat
    | [] => 0
    | e :: es => crepExprFuel e + crepExpsFuel es
  termination_by es => sizeOf es
end

theorem loopExprFuel_append {width : Nat} [NeZero width]
    (a b : List (HolLoopProg width)) (fa fb : Nat)
    (first : loopExprFuel (loopNestedSeqHOL a) = some fa)
    (second : loopExprFuel (loopNestedSeqHOL b) = some fb) :
    loopExprFuel (loopNestedSeqHOL (a ++ b)) = some (fa + fb) := by
  induction a generalizing fa with
  | nil =>
    simp [loopNestedSeqHOL,loopExprFuel] at first
    subst fa
    simpa only [List.nil_append,Nat.zero_add] using second
  | cons head rest ih =>
    cases hh : loopExprFuel head with
    | none => simp [loopNestedSeqHOL,loopExprFuel,hh] at first
    | some fh =>
      cases ht : loopExprFuel (loopNestedSeqHOL rest) with
      | none => simp [loopNestedSeqHOL,loopExprFuel,hh,ht] at first
      | some ft =>
        simp [loopNestedSeqHOL,loopExprFuel,hh,ht] at first
        subst fa
        have tail := ih ft ht
        simp only [List.cons_append,loopNestedSeqHOL,loopExprFuel,hh]
        rw [tail]
        simp [Nat.add_assoc]

theorem loopAssignments_fuel {width : Nat} [NeZero width]
    (offsets : List Nat) (values : List (HolLoopExp width)) (start : Nat) :
    loopExprFuel (loopNestedSeqHOL (offsets.zipWith
      (fun offset value => HolLoopProg.assign (start + offset) value) values)) = some 0 := by
  induction offsets generalizing values with
  | nil => rfl
  | cons offset rest ih =>
    cases values with
    | nil => rfl
    | cons value tail => simp [List.zipWith,loopNestedSeqHOL,loopExprFuel,ih]

mutual
  /-- Every expression compiler output has the exact comparison-count budget. -/
  theorem compileExp_fuel {width : Nat} [NeZero width]
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) (e : CrepExpHOL width) :
      loopExprFuel (loopNestedSeqHOL (compileExpHOLExact ctxt tmp live e).1) = some (crepExprFuel e) := by
    cases e
    case load e =>
      rcases compiled : compileExpHOLExact ctxt tmp live e with ⟨code,value,next,out⟩
      have child := compileExp_fuel ctxt tmp live e
      rw [compiled] at child
      simpa only [compileExpHOLExact,compiled,crepExprFuel] using child
    case loadByte e =>
      rcases compiled : compileExpHOLExact ctxt tmp live e with ⟨code,value,next,out⟩
      have child := compileExp_fuel ctxt tmp live e
      rw [compiled] at child
      simpa [compileExpHOLExact,compiled,crepExprFuel] using
        loopExprFuel_append code [.assign next value,.loadByte next next] _ 0 child rfl
    case load32 e =>
      rcases compiled : compileExpHOLExact ctxt tmp live e with ⟨code,value,next,out⟩
      have child := compileExp_fuel ctxt tmp live e
      rw [compiled] at child
      simpa [compileExpHOLExact,compiled,crepExprFuel] using
        loopExprFuel_append code [.assign next value,.load32 next next] _ 0 child rfl
    case op operator es =>
      rcases compiled : compileExpsHOLExact ctxt tmp live es with ⟨code,values,next,out⟩
      have children := compileExps_fuel ctxt tmp live es
      rw [compiled] at children
      simpa only [compileExpHOLExact,compiled,crepExprFuel] using children
    case shift operator a b =>
      rcases left : compileExpHOLExact ctxt tmp live a with ⟨ac,av,an,al⟩
      rcases right : compileExpHOLExact ctxt an al b with ⟨bc,bv,bn,bl⟩
      have first := compileExp_fuel ctxt tmp live a
      have second := compileExp_fuel ctxt an al b
      rw [left] at first
      rw [right] at second
      simpa only [compileExpHOLExact,left,right,crepExprFuel] using
        loopExprFuel_append ac bc _ _ first second
    case cmp operator a b =>
      rcases left : compileExpHOLExact ctxt tmp live a with ⟨ac,av,an,al⟩
      rcases right : compileExpHOLExact ctxt an al b with ⟨bc,bv,bn,bl⟩
      have first := compileExp_fuel ctxt tmp live a
      have second := compileExp_fuel ctxt an al b
      rw [left] at first
      rw [right] at second
      have combined := loopExprFuel_append ac bc _ _ first second
      have tail : loopExprFuel (loopNestedSeqHOL
          [.assign (bn + 1) av,.assign (bn + 2) bv,
           .ite operator (bn + 1) (.reg (bn + 2))
             (.assign (bn + 1) (.const 1)) (.assign (bn + 1) (.const 0))
             (sptListInsert [bn + 1,bn + 2] bl)]) = some 1 := by
        simp [loopNestedSeqHOL,loopExprFuel]
      simpa only [compileExpHOLExact,left,right,crepExprFuel,progIfHOLExact,List.append_assoc] using
        loopExprFuel_append (ac ++ bc) _ _ 1 combined tail
    case crepOp operator es =>
      rcases compiled : compileExpsHOLExact ctxt tmp live es with ⟨code,values,next,out⟩
      rcases operation : compileCrepopHOLExact (width := width) operator ctxt.target next (next + 1) (next + values.length)
          (sptListInsert ((List.range values.length).map (fun offset => next + offset)) out) with ⟨ops,dest⟩
      have children := compileExps_fuel ctxt tmp live es
      rw [compiled] at children
      have assigns := loopAssignments_fuel (List.range values.length) values next
      have opsFuel : loopExprFuel (loopNestedSeqHOL ops) = some 0 := by
        cases operator
        by_cases arm : ctxt.target = Compiler.Encoders.Asm.AsmArchitecture.armv7
        · simp only [compileCrepopHOLExact,if_pos arm,Prod.mk.injEq] at operation
          obtain ⟨rfl,rfl⟩ := operation
          rfl
        · simp only [compileCrepopHOLExact,if_neg arm,Prod.mk.injEq] at operation
          obtain ⟨rfl,rfl⟩ := operation
          rfl
      have prefixFuel := loopExprFuel_append code _ _ 0 children assigns
      have full := loopExprFuel_append _ ops _ 0 prefixFuel opsFuel
      simpa [compileExpHOLExact,compiled,operation,crepExprFuel] using full
    all_goals simp [compileExpHOLExact,loopNestedSeqHOL,loopExprFuel,crepExprFuel]
  termination_by sizeOf e
  decreasing_by all_goals simp_all <;> omega

  /-- Argument lists sum the static budgets of their emitted expressions. -/
  theorem compileExps_fuel {width : Nat} [NeZero width]
      (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) (es : List (CrepExpHOL width)) :
      loopExprFuel (loopNestedSeqHOL (compileExpsHOLExact ctxt tmp live es).1) = some (crepExpsFuel es) := by
    cases es with
    | nil => simp [compileExpsHOLExact,loopNestedSeqHOL,loopExprFuel,crepExpsFuel]
    | cons e es =>
      rcases head : compileExpHOLExact ctxt tmp live e with ⟨code,value,next,out⟩
      rcases tail : compileExpsHOLExact ctxt next out es with ⟨rest,values,final,finalLive⟩
      have first := compileExp_fuel ctxt tmp live e
      have second := compileExps_fuel ctxt next out es
      rw [head] at first
      rw [tail] at second
      simpa only [compileExpsHOLExact,head,tail,crepExpsFuel] using
        loopExprFuel_append code rest _ _ first second
  termination_by sizeOf es
  decreasing_by all_goals simp_all <;> omega
end

mutual
  theorem crepExprFuel_le_size {width : Nat} [NeZero width] (e : CrepExpHOL width) :
      crepExprFuel e ≤ sizeOf e := by
    cases e
    case load e => have h := crepExprFuel_le_size e; simp only [crepExprFuel,CrepExpHOL.load.sizeOf_spec]; omega
    case loadByte e => have h := crepExprFuel_le_size e; simp only [crepExprFuel,CrepExpHOL.loadByte.sizeOf_spec]; omega
    case load32 e => have h := crepExprFuel_le_size e; simp only [crepExprFuel,CrepExpHOL.load32.sizeOf_spec]; omega
    case op operator es => have h := crepExpsFuel_le_size es; simp only [crepExprFuel,CrepExpHOL.op.sizeOf_spec]; omega
    case crepOp operator es => have h := crepExpsFuel_le_size es; simp only [crepExprFuel,CrepExpHOL.crepOp.sizeOf_spec]; omega
    case cmp operator a b =>
      have first := crepExprFuel_le_size a
      have second := crepExprFuel_le_size b
      simp only [crepExprFuel,CrepExpHOL.cmp.sizeOf_spec]
      omega
    case shift operator a b =>
      have first := crepExprFuel_le_size a
      have second := crepExprFuel_le_size b
      simp only [crepExprFuel,CrepExpHOL.shift.sizeOf_spec]
      omega
    all_goals simp [crepExprFuel]
  termination_by sizeOf e
  decreasing_by all_goals simp_all <;> omega

  theorem crepExpsFuel_le_size {width : Nat} [NeZero width] (es : List (CrepExpHOL width)) :
      crepExpsFuel es ≤ sizeOf es := by
    cases es with
    | nil => simp [crepExpsFuel]
    | cons e es =>
      have first := crepExprFuel_le_size e
      have rest := crepExpsFuel_le_size es
      simp only [crepExpsFuel,List.cons.sizeOf_spec]
      omega
  termination_by sizeOf es
  decreasing_by all_goals simp_all <;> omega
end

#print axioms crepExprFuel_le_size
#print axioms crepExpsFuel_le_size
#print axioms compileExp_fuel
#print axioms compileExps_fuel
#print axioms loopExprFuel_append
#print axioms loopAssignments_fuel
end InitECandidate.Runtime
