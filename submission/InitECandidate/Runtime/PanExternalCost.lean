import InitECandidate.Runtime.PanTotalExpressionCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

noncomputable def sourceReadBytes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (address length : BitVec 64) : Option (List (BitVec 8)) :=
  readBytearrayWordHOL (byteWidth := 8) address length.toNat
    (@panMemLoadByteWord8HOL 64 _ s.memory s.memaddrs
      (fun a => Classical.propDecidable (s.memaddrs a)) s.be)

/-- Input read attempts conservatively charge the requested byte counts.
The native event is charged only after both byte arrays have been read;
returning calls additionally charge the actual returned byte count. -/
noncomputable def externalTransferEvents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (function : MlStringHOL) (configuration configurationLength array arrayLength : ExpHOL 64) :
    List WorkEvent :=
  match expressionValue s configuration, expressionValue s configurationLength,
      expressionValue s array, expressionValue s arrayLength with
  | some (.val (.word a)), some (.val (.word n)),
      some (.val (.word b)), some (.val (.word m)) =>
      .transfer (n.toNat + m.toNat) ::
        (match sourceReadBytes s a n, sourceReadBytes s b m with
         | some first, some second =>
             match callFFIHOL s.ffi (.extCall function) first second with
             | .final _ => [.nativeEvent]
             | .ret _ returned => [.nativeEvent, .transfer returned.length]
         | _, _ => [])
  | _, _, _, _ => []

noncomputable def externalEvents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (function : MlStringHOL) (configuration configurationLength array arrayLength : ExpHOL 64) :
    List WorkEvent :=
  .statement :: (expressionEvents s configuration ++ expressionEvents s configurationLength ++
    expressionEvents s array ++ expressionEvents s arrayLength ++
    externalTransferEvents s function configuration configurationLength array arrayLength)

/-- Shared-memory source clauses perform one bounded-size external operation.
The event is a conservative allowance after well-typed operands; domain or
oracle rejection may terminate before the event. Width-specific native costs
must be certified separately. -/
noncomputable def sharedLoadEvents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (kind : VarKind) (name : MlStringHOL) (address : ExpHOL 64) : List WorkEvent :=
  .statement :: (expressionEvents s address ++
    (match expressionValue s address, lookupKvarHOLFinite kind name s with
     | some (.val (.word _)), some (.val (.word _)) => [.nativeEvent, .copy 1]
     | _, _ => []))

noncomputable def sharedStoreEvents {F : Type} (s : PanSemStateFiniteExact 64 F)
    (address value : ExpHOL 64) : List WorkEvent :=
  .statement :: (expressionEvents s address ++ expressionEvents s value ++
    (if expressionIsWord s address && expressionIsWord s value then [.nativeEvent] else []))

/-- Returning external calls charge output size in addition to both input requests. -/
theorem external_transfer_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (function : MlStringHOL) (e1 e2 e3 e4 : ExpHOL 64) (a n b m : BitVec 64)
    (first second returned : List (BitVec 8)) (ffi)
    (h1 : expressionValue s e1 = some (.val (.word a)))
    (h2 : expressionValue s e2 = some (.val (.word n)))
    (h3 : expressionValue s e3 = some (.val (.word b)))
    (h4 : expressionValue s e4 = some (.val (.word m)))
    (read1 : sourceReadBytes s a n = some first)
    (read2 : sourceReadBytes s b m = some second)
    (call : callFFIHOL s.ffi (.extCall function) first second = .ret ffi returned) :
    externalTransferEvents s function e1 e2 e3 e4 =
      [.transfer (n.toNat + m.toNat), .nativeEvent, .transfer returned.length] := by
  simp only [externalTransferEvents, h1, h2, h3, h4, read1, read2, call]

#print axioms external_transfer_return
end InitECandidate.Runtime.FineCost
