import InitE.SourceSemantics
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang

def sourceEntryCode {width : Nat} [NeZero width] {F : Type}
    (state : PanSemStateFiniteExact width F) (locals : HolFiniteMapExact MlS (ValueHOL width))
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :=
  {state with locals := locals,code := code}

theorem sourceEntryCode_code {width : Nat} [NeZero width] {F : Type}
    (state : PanSemStateFiniteExact width F) (locals : HolFiniteMapExact MlS (ValueHOL width))
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    (sourceEntryCode state locals code).code = code := rfl

theorem sourceEntryCode_replace {width : Nat} [NeZero width] {F : Type}
    (state : PanSemStateFiniteExact width F) (locals : HolFiniteMapExact MlS (ValueHOL width))
    (code next : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    {sourceEntryCode state locals code with code := next} = sourceEntryCode state locals next := rfl
end InitECandidate.Runtime
