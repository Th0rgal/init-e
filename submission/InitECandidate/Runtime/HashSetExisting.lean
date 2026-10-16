import InitECandidate.Runtime.HashGetTail
import InitECandidate.Runtime.HashOccupancyPreservation
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def hashSetValueAddress : ExpHOL 64 :=
  .op .add [.load .one (hashLocalAddress (ofString "t") 40),.panop .mul [.var .local (ofString "i"),.const 8]]

def hashSetExistingTail (missing : ProgHOL 64) : ProgHOL 64 :=
  .seq (.ite (.cmp .notEqual (.var .local (ofString "i")) (.load .one (hashLocalAddress (ofString "t") 16)))
      (.seq (.store hashSetValueAddress (.var .local (ofString "value"))) (.return (.const 0))) .skip) missing

def hashSetMissing : ProgHOL 64 :=
  match declToHOLStructural Guest.guestFn_htab_set with
  | .function fn => match fn.body with | .decCall _ _ _ _ (.seq _ rest) => rest | _ => .skip
  | _ => .skip

theorem source_hashSet_existing : sourceFunctionBody Guest.guestFn_htab_set =
    .decCall (ofString "i") .one (ofString "htab_find_slot")
      [.var .local (ofString "t"),.var .local (ofString "key")] (hashSetExistingTail hashSetMissing) := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

/-- Updating an existing slot stores only its value and returns immediately,
without reaching growth/insertion and without spending source clocks. -/
theorem evaluate_hashSet_existing_tail {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table index capacity values value : BitVec 64) (missing : ProgHOL 64)
    (different : index ≠ capacity)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain40 : state.memaddrs (table + 40)) (cell40 : state.memory (table + 40) = .word values)
    (valueDomain : state.memaddrs (values + index * 8)) :
    evaluateHOLFiniteState state (hashSetExistingTail missing) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite (sourceWriteWord state (values + index * 8) value)) := by
  have d16 : state.memaddrs (table + 16#64) := domain16
  have c16 : state.memory (table + 16#64) = .word capacity := cell16
  have d40 : state.memaddrs (table + 40#64) := domain40
  have c40 : state.memory (table + 40#64) = .word values := cell40
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.var .local (ofString "i")) (.load .one (hashLocalAddress (ofString "t") 16))) =
      some (.val (.word (1 : BitVec 64))) := by
    simp [evalHOLExact,evalListHOLExact,hashLocalAddress,tableLocal,indexLocal,wordOpHOL,wordOp,
      valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,d16,c16,Compiler.Encoders.Asm.wordCmpHOL]
    exact different
  have address : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) hashSetValueAddress =
      some (.val (.word (values + index * 8))) := by
    simp [hashSetValueAddress,evalHOLExact,evalListHOLExact,hashLocalAddress,tableLocal,indexLocal,wordOpHOL,wordOp,
      panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,d40,c40]
  have store := evaluate_store_word state (values + index * 8) value hashSetValueAddress (.var .local (ofString "value"))
    address valueLocal valueDomain
  unfold hashSetExistingTail
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition]
  simp only [show ¬(1 : BitVec 64) = 0 by decide]
  rw [evaluateHOLFiniteState_seq_line780,store]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

/-- Existing-value updates preserve actual occupancy counts when the value
cell is outside the occupancy array's aligned cells. -/
theorem hashSet_existing_count {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used destination value : BitVec 64)
    (separate : ∀ index : BitVec 64, index.toNat < capacity.toNat → panByteAlignHOL (used + index) ≠ destination) :
    hashOccupiedCount capacity (hashOccupancyRead (emptyLocalsHOLFinite (sourceWriteWord state destination value)) used) =
      hashOccupiedCount capacity (hashOccupancyRead state used) :=
  sourceWriteWord_occupancy_preserved state capacity used destination value separate

/-- The constructor layout places the value array before occupancy. Every
in-range value update is therefore separate from every occupancy cell. -/
theorem hashSet_value_separate (values used capacity index : BitVec 64)
    (inside : index.toNat < capacity.toNat)
    (valuesAligned : values.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (ordered : values.toNat + capacity.toNat * 8 ≤ used.toNat)
    (bounded : used.toNat + capacity.toNat ≤ 33806089496) :
    ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + index * 8 := by
  have interval := hashFind_slot_offset values index 8 capacity 8 0 inside
    (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
    valuesAligned (by decide) (by decide) (by decide)
  have upper : (values + index * 8).toNat < values.toNat + capacity.toNat * 8 := by
    simpa using interval.2.2
  apply hashOccupancy_separate_allocation used capacity (values + index * 8) usedAligned (by omega)
  exact Or.inl (by omega)

#print axioms hashSet_value_separate
#print axioms source_hashSet_existing
#print axioms evaluate_hashSet_existing_tail
#print axioms hashSet_existing_count
end InitECandidate.Runtime
