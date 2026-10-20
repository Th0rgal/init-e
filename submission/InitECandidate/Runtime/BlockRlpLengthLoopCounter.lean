import InitECandidate.Runtime.VariableCountedDeclaration
import InitECandidate.Runtime.PanDecCallUnconditionalNormalScope
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Semantic single-counter increment, allowing real declarations and declaration calls. -/
def BlockRlpCounterAdvances (counter : MlS) (program : ProgHOL 64) : Prop :=
 ∀ {F : Type} (s post : PanSemStateFiniteExact 64 F) (w : BitVec 64),
 s.locals.lookup counter=some (.val (.word w)) →evaluateHOLFiniteState s program=(none,post) →
 post.locals.lookup counter=some (.val (.word (w+1)))
theorem block_rlp_counter_incr (counter : MlS) : BlockRlpCounterAdvances counter
 (.assign .local counter (.op .add [.var .local counter,.const 1])) := by
 intro F s post w atCounter run
 have actual : evaluateHOLFiniteState s (.assign .local counter (.op .add [.var .local counter,.const 1]))=
  (none,setVarHOLFinite counter (.val (.word (w+1))) s) := by
  simp [evaluateHOLFiniteState_assign,evalHOLExact,evalListHOLExact,atCounter,wordOpHOL,wordOp,valueIsWord,
   valueWord,lookupKvarHOLExact,isValidValueHOLExact,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL]
 rw [actual] at run
 cases Prod.mk.inj run |>.2
 simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
theorem block_rlp_counter_seq (counter : MlS) (first tail : ProgHOL 64)
 (avoid : avoidsLocal counter first=true) (advance : BlockRlpCounterAdvances counter tail) :
 BlockRlpCounterAdvances counter (.seq first tail) := by
 intro F s post w atCounter run
 rw [evaluateHOLFiniteState_seq_line780] at run
 cases firstRun : evaluateHOLFiniteState s first with
 | mk result middle=>
  rw [firstRun] at run
  cases result with
  | some r=>cases run
  | none=>
   have kept:=evaluate_avoidsLocal_flowing counter first avoid s (by rw [firstRun];exact Or.inl rfl)
   rw [firstRun] at kept
   exact advance middle post w (kept.trans atCounter) run
theorem block_rlp_counter_dec (counter name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
 (body : ProgHOL 64) (different : name≠counter) (advance : BlockRlpCounterAdvances counter body) :
 BlockRlpCounterAdvances counter (.dec name shape initializer body) := by
 intro F s post w atCounter run
 obtain ⟨value,output,_,bodyRun,restored⟩:=evaluate_dec_normal_scope s post name shape initializer body run
 have entered : (setVarHOLFinite name value s).locals.lookup counter=some (.val (.word w)) := by
  simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different] using atCounter
 have advanced:=advance _ output w entered bodyRun
 rw [restored]
 change (HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)).lookup counter=_
 rw [resVarEq_lookup,if_neg (Ne.symm different)]
 exact advanced
theorem block_rlp_counter_decCall (counter name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
 (body : ProgHOL 64) (different : name≠counter) (advance : BlockRlpCounterAdvances counter body) :
 BlockRlpCounterAdvances counter (.decCall name shape function arguments body) := by
 intro F s post w atCounter run
 obtain ⟨value,ready,output,locals,bodyRun,restored⟩:=evaluate_decCall_unconditional_normal_scope s post name function shape arguments body run
 have entered : (setVarHOLFinite name value ready).locals.lookup counter=some (.val (.word w)) := by
  simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals] using atCounter
 have advanced:=advance _ output w entered bodyRun
 rw [restored]
 change (HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)).lookup counter=_
 rw [resVarEq_lookup,if_neg (Ne.symm different)]
 exact advanced
structure BlockRlpCountedBody (counter : MlS) (body : ProgHOL 64) (cost : Nat) : Prop where
 bounded : ProgBounded body cost
 noContinue : noTopContinue body=true
 advances : BlockRlpCounterAdvances counter body
theorem BlockRlpCountedBody.run {counter : MlS} {body : ProgHOL 64} {cost : Nat}
 (counted : BlockRlpCountedBody counter body cost) {F : Type} (s : PanSemStateFiniteExact 64 F)
 (code : s.code=originalRuntimeCode) (w : BitVec 64) (atCounter : s.locals.lookup counter=some (.val (.word w)))
 (budget : cost≤s.clock) :
 s.clock≤(evaluateHOLFiniteState s body).2.clock+cost ∧(evaluateHOLFiniteState s body).2.clock≤s.clock ∧
 (evaluateHOLFiniteState s body).1≠some .timeOut ∧(evaluateHOLFiniteState s body).1≠some .continue ∧
 ((evaluateHOLFiniteState s body).1=none→(evaluateHOLFiniteState s body).2.locals.lookup counter=some (.val (.word (w+1))) ∧
 (evaluateHOLFiniteState s body).2.code=s.code) := by
 obtain ⟨spent,kept,safe⟩:=counted.bounded s code budget
 refine ⟨spent,kept,safe,evaluate_noTopContinue body counted.noContinue s,?_⟩
 intro normal
 exact ⟨counted.advances s _ w atCounter (Prod.ext normal rfl), (evaluateHOLFiniteState_metadata s body).1⟩
#print axioms block_rlp_counter_decCall
#print axioms BlockRlpCountedBody.run
end InitECandidate.Runtime
