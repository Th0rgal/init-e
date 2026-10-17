import InitECandidate.Runtime.RlpReadLengthBodyAgreement
import InitECandidate.Runtime.RlpReadLengthAfterCheckRangeAgreement
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpReadLength_body_returned_range_agreement {F : Type}
    (first second firstPost secondPost : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (firstValue secondValue : ValueHOL 64)
    (p1 : first.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (n1 : first.locals.lookup (ofString "n") = some (.val (.word length)))
    (p2 : second.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (n2 : second.locals.lookup (ofString "n") = some (.val (.word length)))
    (code1 : first.code = originalRuntimeCode) (code2 : second.code = originalRuntimeCode)
    (reads : ∀ offset : BitVec 64, offset.toNat < length.toNat → @panMemLoadByteHOL 64 _ first.memory first.memaddrs
        (fun address => Classical.propDecidable (first.memaddrs address)) first.be (pointer + offset) =
      @panMemLoadByteHOL 64 _ second.memory second.memaddrs
        (fun address => Classical.propDecidable (second.memaddrs address)) second.be (pointer + offset))
    (run1 : evaluateHOLFiniteState first (sourceFunctionBody Guest.guestFn_rlp_read_length) = (some (.returned firstValue),firstPost))
    (run2 : evaluateHOLFiniteState second (sourceFunctionBody Guest.guestFn_rlp_read_length) = (some (.returned secondValue),secondPost)) :
    firstValue = secondValue := by
  exact rlpReadLength_after_check_range_agreement first second firstPost secondPost pointer length firstValue secondValue p1 n1 p2 n2 reads
    (rlpReadLength_body_returned_after_check first firstPost firstValue code1 run1)
    (rlpReadLength_body_returned_after_check second secondPost secondValue code2 run2)

#print axioms rlpReadLength_body_returned_range_agreement
end InitECandidate.Runtime
