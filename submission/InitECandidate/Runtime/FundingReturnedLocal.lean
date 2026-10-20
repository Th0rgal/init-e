import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.AvoidsLocalFrame
import InitECandidate.Runtime.EncodeHeaderReturnedPlan
import InitECandidate.Runtime.EncodeHeaderReturnedDeclarationContext
import InitECandidate.Runtime.HtabInsertRawFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Syntactically checked caller-local return; real calls may fail/throw, but
successful returns cannot substitute an arbitrary callee result for this local. -/
def fundingReturnLocal (key : MlS) : ProgHOL 64→Bool
 | .return (.var .local name)=>name==key
 | .seq first tail=>noDirectReturn first &&avoidsLocal key first &&fundingReturnLocal key tail
 | .dec name _ _ body=>!(name==key)&&fundingReturnLocal key body
 | .decCall name _ _ _ body=>!(name==key)&&fundingReturnLocal key body
 | _=>false

theorem funding_return_local {F : Type} (program : ProgHOL 64) (key : MlS)
 (supported : fundingReturnLocal key program=true) (s post : PanSemStateFiniteExact 64 F)
 (saved value : ValueHOL 64) (atKey : s.locals.lookup key=some saved)
 (run : evaluateHOLFiniteState s program=(some (.returned value),post)) : value=saved := by
 cases shape : program with
 | seq first tail=>
  have children : noDirectReturn first=true ∧avoidsLocal key first=true ∧fundingReturnLocal key tail=true := by
   simpa [shape,fundingReturnLocal,Bool.and_eq_true,and_assoc] using supported
  obtain ⟨middle,normal,returned⟩:=encode_header_seq_returned_of_no_return s post first tail value
   (fun v=>evaluate_noDirectReturn first children.1 s v) (by simpa [shape] using run)
  have kept:=evaluate_avoidsLocal_flowing key first children.2.1 s (by rw [normal];exact Or.inl rfl)
  rw [normal] at kept
  exact funding_return_local tail key children.2.2 middle post saved value (kept.trans atKey) returned
 | dec name kind initializer body=>
  have different : key≠name := by intro equal;subst name;simp [shape,fundingReturnLocal] at supported
  have child : fundingReturnLocal key body=true := by simpa [shape,fundingReturnLocal,Ne.symm different] using supported
  obtain ⟨initial,inner,_,returned,_⟩:=dec_returned_state (by simpa [shape] using run)
  exact funding_return_local body key child (setVarHOLFinite name initial s) inner saved value
   (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different] using atKey) returned
 | decCall name kind function arguments body=>
  have different : key≠name := by intro equal;subst name;simp [shape,fundingReturnLocal] at supported
  have child : fundingReturnLocal key body=true := by simpa [shape,fundingReturnLocal,Ne.symm different] using supported
  obtain ⟨values,calleeBody,callee,returnShape,returned,bodyPost,ready,output,_,_,_,locals,_,_,_,_,_,_,tailRun,_⟩:=
   encode_header_returned_declaration_context s post name function kind arguments body value (by simpa [shape] using run)
  apply funding_return_local body key child (setVarHOLFinite name returned ready) output saved value _ tailRun
  change (ready.locals.update (name,returned)).lookup key=some saved
  rw [locals]
  simpa [HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different] using atKey
 | «return» expression=>
  cases expression with
  | var kind name=>
   cases kind with
   | global=>simp [shape,fundingReturnLocal] at supported
   | «local»=>
    have same : name=key := by simpa [shape,fundingReturnLocal] using supported
    subst name
    have result:=(Prod.mk.inj run).1
    rw [shape] at result
    change (evaluateHOLFiniteState s (.return (.var .local key))).1=some (.returned value) at result
    rw [evaluateHOLFiniteState_return] at result
    simp only [evalHOLExact,atKey] at result
    split at result
    · simpa using result.symm
    · simp at result
  | _=>simp [shape,fundingReturnLocal] at supported
 | _=>simp [shape,fundingReturnLocal] at supported
termination_by sizeOf program
decreasing_by all_goals simp_all <;>omega
#print axioms funding_return_local
end InitECandidate.Runtime
