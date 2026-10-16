import InitECandidate.Runtime.CrepExpressionFuel
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly
namespace InitECandidate.Runtime
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Full original statement compiler property with a numerical extra-fuel bound. -/
def BoundedCrepPropertyAt {width : Nat} [NeZero width] {F : Type}
    (program : CrepProgHOL width) (source : CrepSemHOLState width F) (budget : Nat) : Prop :=
  ∀ (result : Option (CrepResultHOLExact width))
    (sourceFinal : CrepSemHOLState width F),
    ∀ (target : LoopSemStateFiniteExact width F)
    (context : CrepToLoopContextExact) (live : NumSet),
    evalCrepSemHOLProgExact source program = (result, sourceFinal) →
    result ≠ some .error →
    crepToLoopStateRelExact source target →
    crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs →
    crepToLoopGlobalsRelHOLExact source.globals target.globals →
    crepToLoopCodeRelExact context source.code target.code →
    crepToLoopLocalsRelExact context live source.locals target.locals →
    ∃ (extra : Nat), extra ≤ budget ∧ ∃ (targetResult : Option (LoopResultExact width))
      (targetFinal : LoopSemStateFiniteExact width F),
      LoopSemStateFiniteExact.evaluate (compileHOLExact context live program)
        { target with clock := target.clock + extra } = (targetResult, targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact context sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧
      localsResultRel context live result sourceFinal targetFinal

/-- A static compiled-syntax certificate bounds the original compiler witness;
source clock monotonicity discharges the consumed-clock adjustment. -/
theorem crep_statement_of_static {width : Nat} [NeZero width] {F : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width F) (budget : Nat)
    (syntaxBudget : ∀ ctxt live, ∃ cost, cost ≤ budget ∧
      loopExprFuel (compileHOLExact ctxt live p) = some cost) :
    BoundedCrepPropertyAt p s budget := by
  intro result post target ctxt live run notError related memory globals code locals
  obtain ⟨extra,targetResult,final,evaluated,postRelated,postMemory,postGlobals,postCode,same,postLocals⟩ :=
    crepToLoopNcompileCorrectOf p s result post target ctxt live run notError related memory globals code locals
  obtain ⟨cost,small,supported⟩ := syntaxBudget ctxt live
  have clock := loopExprFuel_correct (compileHOLExact ctxt live p)
    {target with clock := target.clock + extra} cost supported
  rw [evaluated] at clock
  change target.clock + extra ≤ final.clock + cost at clock
  have initialClock : s.clock = target.clock := related.2.2.1
  have finalClock : post.clock = final.clock := postRelated.2.2.1
  have lower := evalCrepSemHOLProgExact_clock_le s p
  rw [run] at lower
  dsimp only at lower
  exact ⟨extra,by omega,targetResult,final,evaluated,postRelated,postMemory,postGlobals,postCode,same,postLocals⟩

theorem crep_skip_bounded {width : Nat} [NeZero width] {F : Type}
    (s : CrepSemHOLState width F) : BoundedCrepPropertyAt .skip s 0 :=
  crep_statement_of_static .skip s 0 (fun _ _ => ⟨0,Nat.le_refl _,by simp [compileHOLExact, loopExprFuel]⟩)

theorem crep_break_bounded {width : Nat} [NeZero width] {F : Type}
    (label : Nat) (s : CrepSemHOLState width F) : BoundedCrepPropertyAt (.break label) s 0 :=
  crep_statement_of_static (.break label) s 0 (fun _ _ => ⟨0,Nat.le_refl _,by simp [compileHOLExact, loopExprFuel]⟩)

theorem crep_continue_bounded {width : Nat} [NeZero width] {F : Type}
    (label : Nat) (s : CrepSemHOLState width F) : BoundedCrepPropertyAt (.continue label) s 0 :=
  crep_statement_of_static (.continue label) s 0 (fun _ _ => ⟨0,Nat.le_refl _,by simp [compileHOLExact, loopExprFuel]⟩)

theorem crep_tick_bounded {width : Nat} [NeZero width] {F : Type}
    (s : CrepSemHOLState width F) : BoundedCrepPropertyAt .tick s 1 :=
  crep_statement_of_static .tick s 1 (fun _ _ => ⟨1,Nat.le_refl _,by simp [compileHOLExact, loopExprFuel]⟩)

theorem crep_raise_bounded {width : Nat} [NeZero width] {F : Type}
    (eid : BitVec width) (s : CrepSemHOLState width F) : BoundedCrepPropertyAt (.raise eid) s 0 :=
  crep_statement_of_static (.raise eid) s 0 (fun _ _ => ⟨0,Nat.le_refl _,by simp [compileHOLExact, loopExprFuel]⟩)

theorem crep_return_bounded {width : Nat} [NeZero width] {F : Type}
    (es : List (CrepExpHOL width)) (s : CrepSemHOLState width F) :
    BoundedCrepPropertyAt (.return es) s (crepExpsFuel es) := by
  apply crep_statement_of_static
  intro ctxt live
  rcases compiled : compileExpsHOLExact ctxt (ctxt.vmax + 1) live es with ⟨code,values,next,out⟩
  have first := compileExps_fuel ctxt (ctxt.vmax + 1) live es
  rw [compiled] at first
  have assigns := loopAssignments_fuel (genTemps next values.length) values 0
  simp only [Nat.zero_add] at assigns
  have head := loopExprFuel_append code _ _ 0 first assigns
  have full := loopExprFuel_append _ [.return (genTemps next values.length)] _ 0 head rfl
  exact ⟨_,Nat.le_refl _,by simpa [compileHOLExact,compiled] using full⟩

theorem crep_assign_bounded {width : Nat} [NeZero width] {F : Type}
    (name : Nat) (e : CrepExpHOL width) (s : CrepSemHOLState width F) :
    BoundedCrepPropertyAt (.assign name e) s (crepExprFuel e) := by
  apply crep_statement_of_static
  intro ctxt live
  cases found : ctxt.vars.lookup name with
  | none => exact ⟨0,Nat.zero_le _,by simp [compileHOLExact,found,loopExprFuel]⟩
  | some mapped =>
    rcases compiled : compileExpHOLExact ctxt (ctxt.vmax + 1) live e with ⟨code,value,next,out⟩
    have first := compileExp_fuel ctxt (ctxt.vmax + 1) live e
    rw [compiled] at first
    have full := loopExprFuel_append code [.assign mapped value] _ 0 first rfl
    exact ⟨_,Nat.le_refl _,by simpa [compileHOLExact,found,compiled] using full⟩

theorem crep_storeGlob_bounded {width : Nat} [NeZero width] {F : Type}
    (address : BitVec 5) (e : CrepExpHOL width) (s : CrepSemHOLState width F) :
    BoundedCrepPropertyAt (.storeGlob address e) s (crepExprFuel e) := by
  apply crep_statement_of_static
  intro ctxt live
  rcases compiled : compileExpHOLExact ctxt (ctxt.vmax + 1) live e with ⟨code,value,next,out⟩
  have first := compileExp_fuel ctxt (ctxt.vmax + 1) live e
  rw [compiled] at first
  have full := loopExprFuel_append code [.setGlobal address value] _ 0 first rfl
  exact ⟨_,Nat.le_refl _,by simpa [compileHOLExact,compiled] using full⟩

theorem crep_store_bounded {width : Nat} [NeZero width] {F : Type}
    (dst src : CrepExpHOL width) (s : CrepSemHOLState width F) :
    BoundedCrepPropertyAt (.store dst src) s (crepExprFuel dst + crepExprFuel src) := by
  apply crep_statement_of_static
  intro ctxt live
  rcases firstCompiled : compileExpHOLExact ctxt (ctxt.vmax + 1) live dst with ⟨dc,address,next,nlive⟩
  rcases secondCompiled : compileExpHOLExact ctxt next nlive src with ⟨sc,value,final,out⟩
  have first := compileExp_fuel ctxt (ctxt.vmax + 1) live dst
  have second := compileExp_fuel ctxt next nlive src
  rw [firstCompiled] at first
  rw [secondCompiled] at second
  have head := loopExprFuel_append dc sc _ _ first second
  have full := loopExprFuel_append _ [.assign final value, .store address final] _ 0 head rfl
  exact ⟨_,Nat.le_refl _,by simpa [compileHOLExact,firstCompiled,secondCompiled] using full⟩

theorem crep_primitive_bounded {width : Nat} [NeZero width] {F : Type}
    (dest args : List Nat) (op : PrimOp) (s : CrepSemHOLState width F) :
    BoundedCrepPropertyAt (.primitive dest op args) s 0 := by
  apply crep_statement_of_static
  intro ctxt live
  refine ⟨0,Nat.le_refl _,?_⟩
  cases hd : dest.mapM ctxt.vars.lookup <;> cases ha : args.mapM ctxt.vars.lookup <;>
    simp [compileHOLExact,hd,ha,loopExprFuel]

theorem crep_shMem_bounded {width : Nat} [NeZero width] {F : Type}
    (op : WordMemOp) (name : Nat) (e : CrepExpHOL width) (s : CrepSemHOLState width F) :
    BoundedCrepPropertyAt (.shMem op name e) s (crepExprFuel e) := by
  apply crep_statement_of_static
  intro ctxt live
  cases found : ctxt.vars.lookup name with
  | none => exact ⟨0,Nat.zero_le _,by simp [compileHOLExact,found,loopExprFuel]⟩
  | some mapped =>
    rcases compiled : compileExpHOLExact ctxt (ctxt.vmax + 1) live e with ⟨code,value,next,out⟩
    have first := compileExp_fuel ctxt (ctxt.vmax + 1) live e
    rw [compiled] at first
    have full := loopExprFuel_append code [.shMem op mapped value] _ 0 first rfl
    exact ⟨_,Nat.le_refl _,by simpa [compileHOLExact,found,compiled] using full⟩

#print axioms crep_primitive_bounded
#print axioms crep_shMem_bounded
#print axioms crep_store_bounded
theorem crep_store32_bounded {width : Nat} [NeZero width] {F : Type}
    (dst src : CrepExpHOL width) (s : CrepSemHOLState width F) :
    BoundedCrepPropertyAt (.store32 dst src) s (crepExprFuel dst + crepExprFuel src) := by
  apply crep_statement_of_static
  intro ctxt live
  rcases firstCompiled : compileExpHOLExact ctxt (ctxt.vmax + 1) live dst with ⟨dc,address,next,nlive⟩
  rcases secondCompiled : compileExpHOLExact ctxt next nlive src with ⟨sc,value,final,out⟩
  have first := compileExp_fuel ctxt (ctxt.vmax + 1) live dst
  have second := compileExp_fuel ctxt next nlive src
  rw [firstCompiled] at first
  rw [secondCompiled] at second
  have head := loopExprFuel_append dc sc _ _ first second
  have full := loopExprFuel_append _ [.assign final address, .assign (final + 1) value, .store32 final (final + 1)] _ 0 head rfl
  exact ⟨_,Nat.le_refl _,by simpa [compileHOLExact,firstCompiled,secondCompiled] using full⟩

#print axioms crep_store32_bounded
theorem crep_storeByte_bounded {width : Nat} [NeZero width] {F : Type}
    (dst src : CrepExpHOL width) (s : CrepSemHOLState width F) :
    BoundedCrepPropertyAt (.storeByte dst src) s (crepExprFuel dst + crepExprFuel src) := by
  apply crep_statement_of_static
  intro ctxt live
  rcases firstCompiled : compileExpHOLExact ctxt (ctxt.vmax + 1) live dst with ⟨dc,address,next,nlive⟩
  rcases secondCompiled : compileExpHOLExact ctxt next nlive src with ⟨sc,value,final,out⟩
  have first := compileExp_fuel ctxt (ctxt.vmax + 1) live dst
  have second := compileExp_fuel ctxt next nlive src
  rw [firstCompiled] at first
  rw [secondCompiled] at second
  have head := loopExprFuel_append dc sc _ _ first second
  have full := loopExprFuel_append _ [.assign final address, .assign (final + 1) value, .storeByte final (final + 1)] _ 0 head rfl
  exact ⟨_,Nat.le_refl _,by simpa [compileHOLExact,firstCompiled,secondCompiled] using full⟩

#print axioms crep_storeByte_bounded
#print axioms crep_return_bounded
#print axioms crep_assign_bounded
#print axioms crep_storeGlob_bounded
#print axioms crep_statement_of_static
#print axioms crep_skip_bounded
#print axioms crep_break_bounded
#print axioms crep_continue_bounded
#print axioms crep_tick_bounded
#print axioms crep_raise_bounded
end InitECandidate.Runtime
