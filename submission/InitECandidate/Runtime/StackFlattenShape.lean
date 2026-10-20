import InitECandidate.Runtime.StackWeightedThenSkipIf
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.StackToLab Flapjack.Compiler.Backend.LabSem

/-! Exact static layout geometry, independent of section/label numbers and
loop destinations. These lengths locate selected bodies; they are not runtime
prices and never charge an unselected body. -/

def stackFlattenShape : HolProg 64 → Bool × Nat
  | .seq a b => ((stackFlattenShape a).1 || (stackFlattenShape b).1,
      (stackFlattenShape a).2 + (stackFlattenShape b).2)
  | .ite _ _ _ a b =>
      let x := stackFlattenShape a
      let y := stackFlattenShape b
      if stackIsSkip a && stackIsSkip b then (false, 0)
      else if stackIsSkip a then (false, 1 + y.2)
      else if stackIsSkip b then (false, 1 + x.2)
      else if x.1 then (y.1, 1 + x.2 + y.2)
      else if y.1 then (x.1, 1 + x.2 + y.2)
      else (x.1 && y.1, 2 + x.2 + y.2)
  | .loop body => (false, 1 + (stackFlattenShape body).2)
  | .call none _ _ => (true, 1)
  | .call (some (body, _, _, _)) _ none =>
      ((stackFlattenShape body).1, 2 + (stackFlattenShape body).2)
  | .call (some (body, _, _, _)) _ (some (handler, _, _)) =>
      ((stackFlattenShape body).1 && (stackFlattenShape handler).1,
        3 + (stackFlattenShape body).2 + (stackFlattenShape handler).2)
  | .halt _ | .raise _ | .ret _ | .break _ | .continue _ | .rawCall _ => (true, 1)
  | .tick | .inst _ | .jumpLower _ _ _ | .locValue _ _ _ | .shMemOp _ _ _
    | .codeBufferWrite _ _ => (false, 1)
  | .ffi _ _ _ _ _ _ | .install _ _ _ _ _ => (false, 2)
  | _ => (false, 0)
termination_by p => sizeOf p

private theorem shape_append {α : Type} (a b : AppList α) :
    appListAppend (.append a b) = appListAppend a ++ appListAppend b :=
  (appListAppend_thm a b []).1
private theorem shape_list {α : Type} (xs : List α) : appListAppend (.list xs) = xs :=
  (appListAppend_thm .nil .nil xs).2.1

private theorem shape_parts {a : Bool} {b : Nat} {c : Bool × Nat} (h : (a, b) = c) :
    a = c.1 ∧ b = c.2 := ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Both the nonreturning flag and exact emitted instruction count depend only
on the source program. Labels, including the Seq tail label, cost no slots. -/
theorem stackFlattenShape_correct (p : HolProg 64) (tail : Bool)
    (sectionId labelId : Nat) (continues breaks : List Nat) :
    let compiled := Flapjack.Compiler.Backend.StackToLab.flattenHOL tail p sectionId labelId continues breaks
    (compiled.2.1, ((appListAppend compiled.1).filter (fun line => !isLabelHOL line)).length) =
      stackFlattenShape p := by
  match p with
  | .seq a b =>
    have ha := stackFlattenShape_correct a false sectionId labelId continues breaks
    have hb := stackFlattenShape_correct b false sectionId
      (Flapjack.Compiler.Backend.StackToLab.flattenHOL false a sectionId labelId continues breaks).2.2 continues breaks
    have ha := shape_parts ha
    simp only [isLabelHOL] at ha
    have hb := shape_parts hb
    simp only [isLabelHOL] at hb
    cases tail <;> simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, stackFlattenShape, shape_append, shape_list,
      List.filter_append, isLabelHOL, ha.1, ha.2, hb.1, hb.2, Nat.add_assoc]
  | .ite cmp reg operand a b =>
    have ha := stackFlattenShape_correct a false sectionId labelId continues breaks
    have hb := stackFlattenShape_correct b false sectionId
      (Flapjack.Compiler.Backend.StackToLab.flattenHOL false a sectionId labelId continues breaks).2.2 continues breaks
    have ha := shape_parts ha
    simp only [isLabelHOL] at ha
    have hb := shape_parts hb
    simp only [isLabelHOL] at hb
    simp only [Flapjack.Compiler.Backend.StackToLab.flattenHOL, stackFlattenShape]
    simp only [← ha.1, ← hb.1]
    split <;> try split <;> try split <;> try split <;> try split
    all_goals simp [shape_append, shape_list, List.filter_append, isLabelHOL,
      ha.2, hb.2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega
  | .loop body =>
    have h := stackFlattenShape_correct body false sectionId (labelId + 2)
      (labelId :: continues) ((labelId + 1) :: breaks)
    have h := shape_parts h
    simp only [isLabelHOL] at h
    simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, stackFlattenShape, shape_append, shape_list,
      List.filter_append, isLabelHOL, h.2, Nat.add_comm]
  | .call none target handler =>
    cases target <;> simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, stackFlattenShape, compileJumpHOL, shape_list, isLabelHOL]
  | .call (some (body, link, returnSection, returnLabel)) target handler =>
    have hb := stackFlattenShape_correct body false sectionId labelId continues breaks
    have hb := shape_parts hb
    simp only [isLabelHOL] at hb
    cases handler with
    | none =>
      cases target <;> simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, stackFlattenShape, compileJumpHOL, shape_append,
        shape_list, List.filter_append, isLabelHOL, hb.1, hb.2, Nat.add_comm] <;> omega
    | some data =>
      rcases data with ⟨handler, hs, hl⟩
      have hh := stackFlattenShape_correct handler false sectionId
        (Flapjack.Compiler.Backend.StackToLab.flattenHOL false body sectionId labelId continues breaks).2.2 continues breaks
      have hh := shape_parts hh
      simp only [isLabelHOL] at hh
      cases target <;> simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, stackFlattenShape, compileJumpHOL, shape_append,
        shape_list, List.filter_append, isLabelHOL, hb.1, hb.2, hh.1, hh.2,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega
  | .skip | .inst _ | .get _ _ | .set _ _ | .opCurrHeap _ _ _ | .jumpLower _ _ _
    | .alloc _ | .storeConsts _ _ _ | .raise _ | .ret _ | .break _ | .continue _
    | .ffi _ _ _ _ _ _ | .tick | .locValue _ _ _ | .install _ _ _ _ _
    | .shMemOp _ _ _ | .codeBufferWrite _ _ | .dataBufferWrite _ _ | .rawCall _
    | .stackAlloc _ | .stackFree _ | .stackStore _ _ | .stackStoreAny _ _
    | .stackLoad _ _ | .stackLoadAny _ _ | .stackGetSize _ | .stackSetSize _
    | .bitmapLoad _ _ | .halt _ =>
    simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, stackFlattenShape, shape_list, isLabelHOL]
termination_by sizeOf p
decreasing_by all_goals decreasing_trivial

theorem stackFlatten_length (p : HolProg 64) (tail : Bool)
    (sectionId labelId : Nat) (continues breaks : List Nat) :
    ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL tail p
      sectionId labelId continues breaks).1).filter (fun line => !isLabelHOL line)).length =
      (stackFlattenShape p).2 :=
  congrArg (fun x : Bool × Nat => x.2) (stackFlattenShape_correct p tail sectionId labelId continues breaks)

theorem stackFlatten_noRet (p : HolProg 64) (tail : Bool)
    (sectionId labelId : Nat) (continues breaks : List Nat) :
    (Flapjack.Compiler.Backend.StackToLab.flattenHOL tail p
      sectionId labelId continues breaks).2.1 = (stackFlattenShape p).1 := by
  have h := shape_parts (stackFlattenShape_correct p tail sectionId labelId continues breaks)
  exact h.1

/-- The previously checked one-empty-arm geometry has the same static length
at every section and label, including inside nested loops. -/
theorem skipIfBodyLength_eq (p : HolProg 64)
    (sectionId labelId : Nat) (continues breaks : List Nat) :
    skipIfBodyLength p sectionId labelId continues breaks = (stackFlattenShape p).2 :=
  stackFlatten_length p false sectionId labelId continues breaks

#print axioms stackFlatten_length
#print axioms stackFlatten_noRet
#print axioms skipIfBodyLength_eq
#print axioms stackFlattenShape_correct
end InitECandidate.Runtime.StackToLab
