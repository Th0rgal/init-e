import InitECandidate.Runtime.MessageCallGasStipendPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual stipend local is exactly the source's zero or literal2300,
with every other caller local retained. -/
theorem message_call_gas_stipend_prefix_exact_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (zeroFlag : BitVec 64) (value : ValueHOL 64)
 (atFlag : s.locals.lookup (ofString "vz")=some (.val (.word zeroFlag)))
 (run : evaluateHOLFiniteState s (messageCallGasAt 1)=(some (.returned value),post)) :
 ∃stipend : BitVec 64,∃ready output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState ready (messageCallGasAt 3)=(some (.returned value),output) ∧
 post.memory=output.memory ∧post.globals=output.globals ∧ready.code=s.code ∧
 ready.locals.lookup (ofString "stipend")=some (.val (.word stipend)) ∧stipend=(if zeroFlag=0 then 2300 else 0) ∧stipend.toNat≤2300 ∧
 (∀key,key≠ofString "stipend" → ready.locals.lookup key=s.locals.lookup key) := by
 have source1 : messageCallGasAt 1=.dec (ofString "stipend") .one (.const 0) (messageCallGasAt 2):=rfl
 have source2 : messageCallGasAt 2=.seq (.ite (.cmp .equal (.var .local (ofString "vz")) (.const 0)) (.assign .local (ofString "stipend") (.const 2300)) .skip) (messageCallGasAt 3):=rfl
 rw [source1] at run
 obtain ⟨initial,output,initialEval,tailRun,postEq⟩:=funding_declaration_returned_context run
 have initialEq : initial=.val (.word (0#64)):=by simpa [evalHOLExact] using initialEval.symm
 subst initial
 let one:=setVarHOLFinite (ofString "stipend") (.val (.word (0#64))) s
 change evaluateHOLFiniteState one (messageCallGasAt 2)=_ at tailRun
 rw [source2] at tailRun
 obtain ⟨chosen,normal,nextRun⟩:=seq_returned_of_nonreturning_first (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) one v) tailRun
 rw [evaluateHOLFiniteState_ite] at normal
 by_cases zero : zeroFlag=0
 · have chosenEq : chosen=setVarHOLFinite (ofString "stipend") (.val (.word (2300#64))) one := by
    simp (config:={decide:=true}) [one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,atFlag,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at normal
    simp [isValidValueHOLExact,lookupKvarHOLExact,shapeOfHOLExact,shapeEqHOL,HolFiniteMapExact.lookup_update,FUPDATE] at normal
    simpa [one,setVarHOLFinite,setKvarHOLFinite] using normal.symm
   subst chosen
   refine ⟨2300,_,output,nextRun,?_,?_,rfl,?_,by simp [zero],by decide,?_⟩
   · rw [postEq]
   · rw [postEq]
   · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   · intro key different
     simp [one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
 · change zeroFlag≠0#64 at zero
   have chosenEq : chosen=one := by
    simp (config:={decide:=true}) [one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,atFlag,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at normal
    exact normal.symm
   subst chosen
   refine ⟨0,one,output,nextRun,?_,?_,rfl,?_,by simp [zero],by decide,?_⟩
   · rw [postEq]
   · rw [postEq]
   · simp [one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   · intro key different
     simp [one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
#print axioms message_call_gas_stipend_prefix_exact_returned
end InitECandidate.Runtime
