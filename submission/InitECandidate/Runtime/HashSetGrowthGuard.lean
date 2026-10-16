import InitECandidate.Runtime.HashSetMissingSelection
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def hashSetGrowthCondition : ExpHOL 64 :=
  .cmp .lower (.load .one (hashLocalAddress (ofString "t") 16))
    (.panop .mul [.op .add [.load .one (hashLocalAddress (ofString "t") 24),.const 1],.const 2])

theorem source_hashSet_missing : hashSetMissing =
    .seq (.ite hashSetGrowthCondition (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) .skip)
      (.seq (.call (some (none,none)) (ofString "htab_insert_raw")
        [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]) (.return (.const 0))) := by
  rfl

/-- The source growth guard is false below its exact half-full threshold;
all arithmetic is proved to fit before relating words to naturals. -/
theorem eval_hashSet_growth_false {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity count : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain24 : state.memaddrs (table + 24)) (cell24 : state.memory (table + 24) = .word count)
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) hashSetGrowthCondition = some (.val (.word 0)) := by
  have limit := capacity.isLt
  have sum : (count + (1 : BitVec 64)).toNat = count.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by change count.toNat + 1 < 2 ^ 64; omega)]
    rfl
  have product : ((count + 1) * (2 : BitVec 64)).toNat = (count.toNat + 1) * 2 := by
    rw [BitVec.toNat_mul_of_lt (by rw [sum]; change (count.toNat + 1) * 2 < 2 ^ 64; omega),sum]
    rfl
  have d16 : state.memaddrs (table + 16#64) := domain16
  have c16 : state.memory (table + 16#64) = .word capacity := cell16
  have d24 : state.memaddrs (table + 24#64) := domain24
  have c24 : state.memory (table + 24#64) = .word count := cell24
  simp [hashSetGrowthCondition,hashLocalAddress,evalHOLExact,evalListHOLExact,tableLocal,wordOpHOL,wordOp,
    valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,d16,c16,d24,c24,panOpHOL,Compiler.Encoders.Asm.wordCmpHOL]
  apply BitVec.le_def.mpr
  change ((count + 1) * (2 : BitVec 64)).toNat ≤ capacity.toNat
  rw [product]
  exact loadFactor

#print axioms source_hashSet_missing
#print axioms eval_hashSet_growth_false
end InitECandidate.Runtime
