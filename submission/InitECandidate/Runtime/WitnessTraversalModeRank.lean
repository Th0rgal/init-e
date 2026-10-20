import InitECandidate.Runtime.WitnessTraversalInvariant
import InitECandidate.Runtime.WitnessDecodeModeStateMeasure
import InitECandidate.Runtime.WitnessResolveModeStateMeasure
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original decode mode strictly decreases the state-derived rank. -/
theorem WitnessTraversalState.decode_decreases {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (decode : mode=1)
    (running : go=1) (budget : decodeStepBodyCost layout.inputLimit+1≤s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeDecodeMode=(none,post)) :
    witnessTraversalStateMeasure layout.frame post<witnessTraversalStateMeasure layout.frame s := by
  obtain ⟨pointer,length,atPointer,atLength,spanLo,spanHi,inputRange,size⟩ := valid.decodeInput decode
  have lengthBound := size.trans valid.inputBound
  have limit:=valid.inputLimitBound
  have scratchLo:=valid.scratchLower
  have scratchHi:=valid.scratchBound
  have db:=valid.scratchBeforeDatabase
  have floor:=valid.databaseBeforeFloor
  have heapLo:=valid.floorBeforeHeap
  have before:=valid.inputBeforeFloor
  have ordered : layout.frame≤scratch := by change layout.frame.toNat≤scratch.toNat;exact scratchLo
  have limit64 : layout.inputLimit+9<2^64 := by omega
  have countLimit : layout.inputLimit*16<2^64 := by omega
  have arena : ∀ a : BitVec 64, layout.frame.toNat≤a.toNat → a.toNat<scratch.toNat → s.memaddrs a := by
    intro a lo hi;exact valid.scratchArena a lo (by omega)
  have heapArena : ∀ a : BitVec 64, heap.toNat≤a.toNat → a.toNat<33806089496 → s.memaddrs a := by
    intro a lo hi;exact valid.heapArena a (by omega) hi
  have beforeFrame : pointer.toNat+length.toNat≤layout.frame.toNat ∨ (scratch.toNat%8=0 ∧ scratch.toNat≤pointer.toNat) := by
    rcases valid.inputBeforeFrame with below | above
    · exact Or.inl (by omega)
    · exact Or.inr ⟨valid.scratchAligned,by omega⟩
  have beforeHeap : pointer.toNat+length.toNat≤heap.toNat := by omega
  have arrayAbove : scratch.toNat≤heap.toNat := by omega
  have floorAbove : scratch.toNat≤layout.persistentFloor := by omega
  have atGo := valid.atGo
  rw [running] at atGo
  have atMode := valid.atMode
  rw [decode] at atMode
  exact witness_decode_mode_state_measure_decreases s post layout.table pointer length scratch layout.frame heap top scratch.toNat layout.inputLimit
    valid.atTop valid.atDb atPointer atLength inputRange lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered
    valid.framePositive (Nat.le_refl _) arena budget valid.atHeap valid.heapBound valid.heapAligned countLimit heapArena
    beforeFrame beforeHeap arrayAbove limit layout.input layout.inputLength layout.persistentFloor floorAbove heapLo spanLo spanHi
    valid.stack atGo atMode run
#print axioms WitnessTraversalState.decode_decreases

/-- The original resolve mode strictly decreases the state-derived rank. -/
theorem WitnessTraversalState.resolve_decreases {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (resolve : mode=2)
    (running : go=1) (budget : resolveStepBodyCost layout.inputLimit+1≤s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeResolveMode=(none,post)) :
    witnessTraversalStateMeasure layout.frame post<witnessTraversalStateMeasure layout.frame s := by
  obtain ⟨array,slot,pointer,length,cell,readable,atSlot,slotBound,entry,lengthBound⟩ :=
    valid.resolve_arguments layout s scratch heap top mode go resolve
  have limit := valid.inputLimitBound
  have scratchLo := valid.scratchLower
  have scratchHi := valid.scratchBound
  have db := valid.scratchBeforeDatabase
  have floor := valid.databaseBeforeFloor
  have heapLo := valid.floorBeforeHeap
  have ordered : layout.frame≤scratch := by change layout.frame.toNat≤scratch.toNat;exact scratchLo
  have limit64 : layout.inputLimit+9<2^64 := by omega
  have arena : ∀ a : BitVec 64, layout.frame.toNat≤a.toNat → a.toNat<scratch.toNat → s.memaddrs a := by
    intro a lo hi;exact valid.scratchArena a lo (by omega)
  have tableAbove : scratch.toNat≤layout.table.toNat := by have h:=valid.tableAboveDatabase;omega
  have arrayAbove : scratch.toNat≤layout.dbArray.toNat := by have h:=valid.arrayAboveDatabase;omega
  have spanSize := entry.length_bound s array slot pointer length layout.input layout.inputLength
  have ticks : resolveStepBodyCost length.toNat+1≤s.clock := by
    have h:=resolveStepBodyCost_mono length.toNat layout.inputLimit lengthBound;omega
  obtain ⟨nonempty,selected⟩ := valid.resolveSelector resolve
  have atGo := valid.atGo
  rw [running] at atGo
  have atMode := valid.atMode
  rw [resolve] at atMode
  exact witness_resolve_mode_state_measure_decreases s post pointer length scratch layout.frame layout.table layout.dbHeap
    layout.dbArray layout.total layout.input layout.inputLength array slot top heap scratch.toNat layout.inputLimit
    valid.atHeap valid.heapBound valid.heapAligned valid.atTop readable cell atSlot entry.readable valid.atDb entry.noWrap lengthBound
    limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena valid.built valid.entries valid.slices
    tableAbove arrayAbove valid.dbArrayEnd entry.startsWithin entry.endsWithin spanSize ticks layout.persistentFloor heapLo valid.stack atGo atMode run
#print axioms WitnessTraversalState.resolve_decreases
end InitECandidate.Runtime
