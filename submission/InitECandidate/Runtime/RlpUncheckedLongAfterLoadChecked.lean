import InitECandidate.Runtime.RlpUncheckedLongDispatchValue
import InitECandidate.Runtime.RlpUncheckedLongStringBranchChecked
import InitECandidate.Runtime.RlpUncheckedLongListBranchChecked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- After-byte unchecked dispatch inherits the checked branch's input bound. -/
theorem rlpUnchecked_long_string_after_load_checked_bound {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (checkedValue uncheckedValue : ValueHOL 64)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedHeader : checked.locals.lookup (ofString "b") = some (.val (.word header)))
    (checkedTotal : checked.locals.lookup (ofString "len") = some (.val (.word total)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (uncheckedHeader : unchecked.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191) (nonzero : total ≠ 0)
    (checkedCode : checked.code = originalRuntimeCode) (uncheckedCode : unchecked.code = originalRuntimeCode)
    (ticks : 10 ≤ checked.clock) (uncheckedTicks : 10 ≤ unchecked.clock)
    (reads : ∀ address, @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
        (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be address =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs
        (fun address => Classical.propDecidable (unchecked.memaddrs address)) unchecked.be address)
    (checkedRun : evaluateHOLFiniteState checked rlpHeaderLongString = (some (.returned checkedValue),checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked rlpUncheckedAfterByte = (some (.returned uncheckedValue),uncheckedPost)) :
    ∃ consumed : BitVec 64, uncheckedValue = .val (.word consumed) ∧ 0 < consumed.toNat ∧ consumed.toNat ≤ total.toNat := by
  rw [evaluate_rlpUnchecked_long_string_after_load unchecked pointer header uncheckedPointer uncheckedHeader lower upper uncheckedCode uncheckedTicks] at uncheckedRun
  exact rlpUnchecked_long_string_branch_checked_bound checked unchecked checkedPost uncheckedPost pointer header total checkedValue uncheckedValue
    checkedPointer checkedHeader checkedTotal uncheckedPointer uncheckedHeader lower upper nonzero checkedCode uncheckedCode ticks reads checkedRun uncheckedRun

#print axioms rlpUnchecked_long_string_after_load_checked_bound

/-- After-byte unchecked dispatch inherits the checked branch's input bound. -/
theorem rlpUnchecked_long_list_after_load_checked_bound {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (checkedValue uncheckedValue : ValueHOL 64)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedHeader : checked.locals.lookup (ofString "b") = some (.val (.word header)))
    (checkedTotal : checked.locals.lookup (ofString "len") = some (.val (.word total)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (uncheckedHeader : unchecked.locals.lookup (ofString "b") = some (.val (.word header)))
    (lower : 247 < header.toNat) (upper : header.toNat ≤ 255) (nonzero : total ≠ 0)
    (checkedCode : checked.code = originalRuntimeCode) (uncheckedCode : unchecked.code = originalRuntimeCode)
    (ticks : 10 ≤ checked.clock) (uncheckedTicks : 10 ≤ unchecked.clock)
    (reads : ∀ address, @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
        (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be address =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs
        (fun address => Classical.propDecidable (unchecked.memaddrs address)) unchecked.be address)
    (checkedRun : evaluateHOLFiniteState checked rlpHeaderLongList = (some (.returned checkedValue),checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked rlpUncheckedAfterByte = (some (.returned uncheckedValue),uncheckedPost)) :
    ∃ consumed : BitVec 64, uncheckedValue = .val (.word consumed) ∧ 0 < consumed.toNat ∧ consumed.toNat ≤ total.toNat := by
  rw [evaluate_rlpUnchecked_long_list_after_load unchecked pointer header uncheckedPointer uncheckedHeader lower upper uncheckedCode uncheckedTicks] at uncheckedRun
  exact rlpUnchecked_long_list_branch_checked_bound checked unchecked checkedPost uncheckedPost pointer header total checkedValue uncheckedValue
    checkedPointer checkedHeader checkedTotal uncheckedPointer uncheckedHeader lower upper nonzero checkedCode uncheckedCode ticks reads checkedRun uncheckedRun

#print axioms rlpUnchecked_long_list_after_load_checked_bound

end InitECandidate.Runtime
