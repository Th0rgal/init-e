import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A successful actual one-word zero declaration has exactly its initialized
body state and its real lexical restoration, without a premise on the body. -/
theorem evaluate_zero_dec_normal_scope {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (body : ProgHOL 64)
 (run : evaluateHOLFiniteState s (.dec name .one (.const (0#64)) body)=(none,post)) :
 ∃output,evaluateHOLFiniteState (setVarHOLFinite name (.val (.word (0#64))) s) body=(none,output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} := by
 obtain ⟨value,output,evaluated,bodyRun,scope⟩:=evaluate_dec_normal_scope s post name .one (.const (0#64)) body run
 have equal : value=.val (.word (0#64)):=Option.some.inj evaluated.symm
 subst value
 exact ⟨output,bodyRun,scope⟩
#print axioms evaluate_zero_dec_normal_scope
end InitECandidate.Runtime
