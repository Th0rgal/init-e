import InitECandidate.Runtime.HashSetGrowthGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem eval_hashSet_growth_true {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity count : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain24 : state.memaddrs (table + 24)) (cell24 : state.memory (table + 24) = .word count)
    (loadFactor : capacity.toNat < (count.toNat + 1) * 2)
    (room : count.toNat < capacity.toNat) (bounded : capacity.toNat ≤ 33806089496) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) hashSetGrowthCondition = some (.val (.word 1)) := by
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
  apply BitVec.lt_def.mpr
  change capacity.toNat < ((count + 1) * (2 : BitVec 64)).toNat
  rw [product]
  exact loadFactor

/-- Above the half-full threshold the actual guard selects the original
installed growth call, without spending a source clock on the guard itself. -/
theorem evaluate_hashSet_growth_selected {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity count : BitVec 64)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain24 : state.memaddrs (table + 24)) (cell24 : state.memory (table + 24) = .word count)
    (loadFactor : capacity.toNat < (count.toNat + 1) * 2)
    (room : count.toNat < capacity.toNat) (bounded : capacity.toNat ≤ 33806089496) :
    evaluateHOLFiniteState state
      (.ite hashSetGrowthCondition (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) .skip) =
    evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) := by
  have condition := eval_hashSet_growth_true state table capacity count tableLocal domain16 cell16 domain24 cell24 loadFactor room bounded
  rw [evaluateHOLFiniteState_ite,condition]
  simp

#print axioms evaluate_hashSet_growth_selected
#print axioms eval_hashSet_growth_true
end InitECandidate.Runtime
