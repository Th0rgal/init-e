import InitECandidate.Runtime.HashGrowRehashRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashGrowRehashArguments : List (ExpHOL 64) :=
  [.var .local (ofString "t"),
   .op .add [.var .local (ofString "keys"),.panop .mul [.var .local (ofString "i"),.var .local (ofString "stride")]],
   .load .one (hashOrderAddress (ofString "vals") (ofString "i"))]

theorem source_hashGrow_rehash_body : hashGrowRehashBody =
    .dec (ofString "i") .one (.load .one (hashOrderAddress (ofString "order") (ofString "k")))
      (.seq (.call (some (none,none)) (ofString "htab_insert_raw") hashGrowRehashArguments)
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"),.const 1]))) := by rfl

/-- The original rehash call reads its old key slot and old value in source
order, without substituting an abstract insertion callback. -/
theorem eval_hashGrow_rehash_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride values index value : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (domain : state.memaddrs (values + index * 8))
    (memory : state.memory (values + index * 8) = .word value) :
    evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      hashGrowRehashArguments = some [.val (.word table),.val (.word (keys + index * stride)),.val (.word value)] := by
  have available : state.memaddrs (values + index * 8#64) := domain
  have cell : state.memory (values + index * 8#64) = .word value := memory
  simp [hashGrowRehashArguments,hashOrderAddress,evalListHOLFinite,evalListHOLExact,evalHOLExact,
    tableLocal,keysLocal,strideLocal,valuesLocal,indexLocal,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,
    isWfShapeExactHOL,memLoadHOLExact,available,cell]

#print axioms source_hashGrow_rehash_body
#print axioms eval_hashGrow_rehash_arguments
end InitECandidate.Runtime
