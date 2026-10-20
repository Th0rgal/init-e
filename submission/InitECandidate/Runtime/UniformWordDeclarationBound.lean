import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.RunBoundedReaches
import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A uniformly bounded installed callee and a continuation bounded for every
actually checked scalar return. Argument and lookup failures are included. -/
theorem uniform_word_declaration_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name function : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (bodyCost tailCost : Nat) (installed : FunBounded function bodyCost)
 (code : s.code=originalRuntimeCode) (budget : bodyCost+1+tailCost≤s.clock)
 (afterReturn : ∀next : PanSemStateFiniteExact 64 F,∀word : BitVec 64,
  next.locals.lookup name=some (.val (.word word))→next.code=originalRuntimeCode→
  tailCost≤next.clock→RunBounded next tail tailCost) :
 RunBounded s (.decCall name .one function arguments tail) (bodyCost+1+tailCost) := by
 cases args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments with
 | none =>
  unfold RunBounded
  rw [evaluateHOLFiniteState_decCall_total,args]
  simp
 | some values =>
  cases lookup : lookupCodeHOLFinite s.code.lookup function values with
  | none =>
   unfold RunBounded
   rw [evaluateHOLFiniteState_decCall_lookup_none s name .one function arguments tail values args lookup]
   simp
  | some data =>
   obtain ⟨body,callee,returnShape⟩:=data
   have bounded : RunBounded (callEntryStateHOLFinite s callee) body bodyCost :=
    ProgBounded.bodies_of_fun installed s code (by omega) values body callee returnShape lookup
   have reached : Reaches s (.decCall name .one function arguments tail)
    (fun next=>(∃word : BitVec 64,next.locals.lookup name=some (.val (.word word))) ∧
     next.code=originalRuntimeCode) (bodyCost+1) tail := by
    apply bounded_decCall_reaches s name function .one returnShape arguments values body tail callee bodyCost _
     args lookup (by omega) bounded
    intro value post run shapes
    obtain ⟨word,rfl⟩:=value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp shapes.1)
    have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
    rw [run] at metadata
    exact ⟨⟨word,by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]⟩,metadata.1.trans code⟩
   exact RunBounded.ofReaches budget reached (by
    intro next facts clock
    obtain ⟨⟨word,binding⟩,installedNext⟩:=facts
    exact afterReturn next word binding installedNext clock)

#print axioms uniform_word_declaration_bounded
end InitECandidate.Runtime
