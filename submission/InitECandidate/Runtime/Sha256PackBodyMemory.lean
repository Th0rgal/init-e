import InitECandidate.Runtime.Sha256BlockSource
import InitECandidate.Runtime.ArithmeticExpressionWord
import InitECandidate.Runtime.WatchedMemoryComposition
import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem shaBlockPack_value_word {F : Type} (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      shaBlockPackValue = some value) : ∃ word : BitVec 64, value = .val (.word word) :=
  eval_binop_returns_word state .or _ value evaluated

theorem shaBlockPack_body_memory {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index accelerator watched : BitVec 64)
    (atIndex : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (small : index.toNat < 4) (fits : accelerator.toNat + 96 ≤ 33806089496)
    (outside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat) :
    (evaluateHOLFiniteState state shaBlockPackBody).2.memory watched = state.memory watched := by
  have mulNatural : (index * (8#64)).toNat = index.toNat * 8 :=
    BitVec.toNat_mul_of_lt (by change index.toNat * 8 < 2 ^ 64; omega)
  have addressNatural : (accelerator + index * (8#64)).toNat = accelerator.toNat + index.toNat * 8 := by
    rw [BitVec.toNat_add_of_lt (by rw [mulNatural]; omega),mulNatural]
  have separate : watched ≠ accelerator + index * (8#64) := by
    intro same
    have natural := congrArg BitVec.toNat same
    rw [addressNatural] at natural
    rcases outside with before | after <;> omega
  rw [source_shaBlock_pack_body]
  apply watched_memory_dec
  intro lo
  apply watched_memory_dec
  intro hi
  apply watched_memory_seq
  · apply evaluate_wordStore_memory_frame _ _ _ (accelerator + index * (8#64)) watched
    · simp (config := {decide := true}) [evalHOLExact,evalListHOLExact,atIndex,atAccel,wordOpHOL,wordOp,
        valueIsWord,valueWord,panOpHOL,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro parsed evaluated
      exact shaBlockPack_value_word _ parsed evaluated
    · exact separate
  · intro next normal
    exact congrFun (evaluate_readOnly_memory _ rfl next) watched

#print axioms shaBlockPack_value_word
#print axioms shaBlockPack_body_memory
end InitECandidate.Runtime
