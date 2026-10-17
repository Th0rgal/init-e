import InitECandidate.Runtime.RlpReadLengthStepValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The exact source state after one successful byte-accumulation step. -/
def rlpReadLengthStepState {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index value : BitVec 64) (byte : UInt8) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "i") (.val (.word (index + 1)))
    (setVarHOLFinite (ofString "v") (.val (.word ((value <<< (8 : Nat)) ||| BitVec.ofNat 64 byte.toNat))) state)

/-- Equal relevant registers and equal byte reads force the same accumulator
update, regardless of unrelated state fields or starting clocks. -/
theorem rlpReadLength_step_agreement {F : Type} (first second firstPost : PanSemStateFiniteExact 64 F)
    (pointer index value : BitVec 64)
    (firstPointer : first.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (firstIndex : first.locals.lookup (ofString "i") = some (.val (.word index)))
    (firstValue : first.locals.lookup (ofString "v") = some (.val (.word value)))
    (secondPointer : second.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (secondIndex : second.locals.lookup (ofString "i") = some (.val (.word index)))
    (secondValue : second.locals.lookup (ofString "v") = some (.val (.word value)))
    (sameRead : @panMemLoadByteHOL 64 _ first.memory first.memaddrs
        (fun address => Classical.propDecidable (first.memaddrs address)) first.be (pointer + index) =
      @panMemLoadByteHOL 64 _ second.memory second.memaddrs
        (fun address => Classical.propDecidable (second.memaddrs address)) second.be (pointer + index))
    (run : evaluateHOLFiniteState first rlpReadLengthStep = (none,firstPost)) :
    ∃ byte : UInt8, firstPost = rlpReadLengthStepState first index value byte ∧
      evaluateHOLFiniteState second rlpReadLengthStep = (none,rlpReadLengthStepState second index value byte) := by
  obtain ⟨byte,loaded,_,_⟩ := rlpReadLength_step_normal_value first firstPost pointer index value firstPointer firstIndex firstValue run
  have firstRun := evaluate_rlpReadLength_step_loaded first pointer index value firstPointer firstIndex firstValue byte loaded
  have secondRun := evaluate_rlpReadLength_step_loaded second pointer index value secondPointer secondIndex secondValue byte
    (sameRead.symm.trans loaded)
  exact ⟨byte,(Prod.mk.inj (run.symm.trans firstRun)).2,secondRun⟩

/-- The corresponding states still agree on the two changing registers. -/
theorem rlpReadLengthStepState_registers {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index value : BitVec 64) (byte : UInt8) :
    (rlpReadLengthStepState state index value byte).locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
    (rlpReadLengthStepState state index value byte).locals.lookup (ofString "v") =
      some (.val (.word ((value <<< (8 : Nat)) ||| BitVec.ofNat 64 byte.toNat))) := by
  simp [rlpReadLengthStepState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "i" ≠ ofString "v" by decide]

#print axioms rlpReadLength_step_agreement
#print axioms rlpReadLengthStepState_registers
end InitECandidate.Runtime
