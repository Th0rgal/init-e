import InitECandidate.Runtime.RlpReadLengthReturnedLoop
import InitECandidate.Runtime.RlpReadLengthLoopRangeAgreement
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Initialized original length readers returning successfully agree on their
decoded value when pointer/count inputs and byte reads agree. -/
theorem rlpReadLength_after_check_range_agreement {F : Type}
    (first second firstPost secondPost : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (firstValue secondValue : ValueHOL 64)
    (p1 : first.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (n1 : first.locals.lookup (ofString "n") = some (.val (.word length)))
    (p2 : second.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (n2 : second.locals.lookup (ofString "n") = some (.val (.word length)))
    (reads : ∀ offset : BitVec 64, offset.toNat < length.toNat → @panMemLoadByteHOL 64 _ first.memory first.memaddrs
        (fun address => Classical.propDecidable (first.memaddrs address)) first.be (pointer + offset) =
      @panMemLoadByteHOL 64 _ second.memory second.memaddrs
        (fun address => Classical.propDecidable (second.memaddrs address)) second.be (pointer + offset))
    (run1 : evaluateHOLFiniteState first rlpReadLengthAfterCheck = (some (.returned firstValue),firstPost))
    (run2 : evaluateHOLFiniteState second rlpReadLengthAfterCheck = (some (.returned secondValue),secondPost)) :
    firstValue = secondValue := by
  obtain ⟨out1,loop1,value1⟩ := rlpReadLength_after_check_returned_loop first firstPost firstValue run1
  obtain ⟨out2,loop2,value2⟩ := rlpReadLength_after_check_returned_loop second secondPost secondValue run2
  have registers : ∀ (state : PanSemStateFiniteExact 64 F),
      state.locals.lookup (ofString "p") = some (.val (.word pointer)) →
      state.locals.lookup (ofString "n") = some (.val (.word length)) →
      (rlpReadLengthInitialState state).locals.lookup (ofString "p") = some (.val (.word pointer)) ∧
      (rlpReadLengthInitialState state).locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) ∧
      (rlpReadLengthInitialState state).locals.lookup (ofString "v") = some (.val (.word (0 : BitVec 64))) ∧
      (rlpReadLengthInitialState state).locals.lookup (ofString "n") = some (.val (.word length)) := by
    intro state pointerLocal lengthLocal
    simp [rlpReadLengthInitialState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,pointerLocal,lengthLocal,
      show ofString "i" ≠ ofString "p" by decide,show ofString "v" ≠ ofString "p" by decide,
      show ofString "i" ≠ ofString "n" by decide,show ofString "v" ≠ ofString "n" by decide,
      show ofString "i" ≠ ofString "v" by decide]
  have firstRegisters := registers first p1 n1
  have secondRegisters := registers second p2 n2
  have equal := rlpReadLength_loop_range_agreement (rlpReadLengthInitialState first) (rlpReadLengthInitialState second) out1 out2
    pointer 0 0 length firstRegisters.1 firstRegisters.2.1 firstRegisters.2.2.1 firstRegisters.2.2.2
    secondRegisters.1 secondRegisters.2.1 secondRegisters.2.2.1 secondRegisters.2.2.2 reads loop1 loop2
  rw [value1,value2] at equal
  exact Option.some.inj equal

#print axioms rlpReadLength_after_check_range_agreement
end InitECandidate.Runtime
