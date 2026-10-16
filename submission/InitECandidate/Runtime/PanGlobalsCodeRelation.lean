import InitECandidate.Runtime.PanGlobalsClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang

/-- Install a source function table and match the current target locals while
retaining every memory, globals, exception and resource invariant. -/
theorem pan_globals_install_code {width : Nat} [NeZero width] {F : Type}
    (context : PanGlobalsContextExact width) (source target : PanSemStateFiniteExact width F)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (related : panGlobalsStateRelHOLExact false context source target)
    (compiled : ∀ name params body shape, code.lookup name = some (params,body,shape) →
      target.code.lookup name = some (params,compileProgExactHOL context body,shape)) :
    panGlobalsStateRelHOLExact true context
      {source with locals := target.locals,code := code} target := by
  obtain ⟨h1,_,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,_,h16,h17,h18,h19⟩ := related
  exact ⟨h1,fun _ => rfl,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,compiled,h16,h17,h18,h19⟩

/-- Supplying a common runtime clock preserves the full initialization relation. -/
theorem pan_globals_relation_clock {width : Nat} [NeZero width] {F : Type}
    (localsEqual : Bool) (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width F) (fuel : Nat)
    (related : panGlobalsStateRelHOLExact localsEqual context source target) :
    panGlobalsStateRelHOLExact localsEqual context {source with clock := fuel} {target with clock := fuel} := by
  obtain ⟨h1,h2,h3,h4,h5,_,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19⟩ := related
  exact ⟨h1,h2,h3,h4,h5,rfl,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19⟩

#print axioms pan_globals_install_code
#print axioms pan_globals_relation_clock
end InitECandidate.Runtime
