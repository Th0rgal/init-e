import InitECandidate.Runtime.HtrRequestListSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem htrRequestList_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer index size roots : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atSize : state.locals.lookup (ofString "sz") = some (.val (.word size)))
    (atRoots : state.locals.lookup (ofString "roots") = some (.val (.word roots))) :
    evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) htrRequestListArguments =
      some [.val (.word (pointer + index * size)),.val (.word (roots + index * (32#64)))] := by
  simp [htrRequestListArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,atPointer,atIndex,atSize,atRoots,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL]

theorem htrRequestList_kind_condition {F : Type} (state : PanSemStateFiniteExact 64 F) (kind tag : BitVec 64)
    (atKind : state.locals.lookup (ofString "kind") = some (.val (.word kind))) :
    @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .equal (.var .local (ofString "kind")) (.const tag)) =
      some (.val (.word (if kind = tag then 1 else 0))) := by
  simp [evalHOLExact,atKind,Compiler.Encoders.Asm.wordCmpHOL]

#print axioms htrRequestList_arguments
#print axioms htrRequestList_kind_condition
end InitECandidate.Runtime
