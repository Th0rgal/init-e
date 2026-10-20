import InitECandidate.Runtime.SourceDomainProgramTransfer
import InitECandidate.Runtime.SourceDomainMemoryTransfer
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The original structured Store transports each actual successful word
write and the destination/source expressions; it assumes no alignment oracle. -/
theorem source_domain_transfer_store (destination source : ExpHOL 64) :
 SourceDomainRunTransfer (.store destination source) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_store] at run ⊢
 cases destinationRun : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) destination with
 | none=>
  rw [destinationRun] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some destinationValue=>
  rw [destinationRun] at run
  rw [eval_source_domain_extend s domain subset destination destinationValue destinationRun]
  cases destinationValue with
  | val payload=>
   cases payload with
   | word address=>
    dsimp only at run ⊢
    cases sourceRun : @evalHOLExact 64 F _ s.toExact
     (fun a=>Classical.propDecidable (s.memaddrs a)) source with
    | none=>
     rw [sourceRun] at run
     exact False.elim (valid (Prod.mk.inj run).1.symm)
    | some value=>
     rw [sourceRun] at run
     rw [eval_source_domain_extend s domain subset source value sourceRun]
     dsimp only at run ⊢
     cases memoryRun : @panMemStoresHOL 64 _ address (flattenHOL value) s.memaddrs
      (fun a=>Classical.propDecidable (s.memaddrs a)) s.memory with
     | none=>
      rw [memoryRun] at run
      exact False.elim (valid (Prod.mk.inj run).1.symm)
     | some memory=>
      rw [memoryRun] at run
      have wide:=@mem_stores_source_domain_extend (flattenHOL value) s.memaddrs domain
       (fun a=>Classical.propDecidable (s.memaddrs a)) (fun a=>Classical.propDecidable (domain a))
       subset address s.memory memory memoryRun
      rw [wide]
      cases run
      rfl
  | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
  | nStruct name fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)

/-- Domain extension preserves the actual successful byte store and its exact memory. -/
theorem source_domain_transfer_store_byte (destination source : ExpHOL 64) :
 SourceDomainRunTransfer (.storeByte destination source) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_storeByte] at run ⊢
 cases destinationRun : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) destination with
 | none=>
  rw [destinationRun] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some destinationValue=>
  rw [destinationRun] at run
  rw [eval_source_domain_extend s domain subset destination destinationValue destinationRun]
  cases destinationValue with
  | val payload=>
   cases payload with
   | word address=>
    dsimp only at run ⊢
    cases sourceRun : @evalHOLExact 64 F _ s.toExact
     (fun a=>Classical.propDecidable (s.memaddrs a)) source with
    | none=>
     rw [sourceRun] at run
     exact False.elim (valid (Prod.mk.inj run).1.symm)
    | some value=>
     rw [sourceRun] at run
     rw [eval_source_domain_extend s domain subset source value sourceRun]
     cases value with
     | val payload=>
      cases payload with
      | word word=>
       dsimp only at run ⊢
       cases memoryRun : @panMemStoreByteWord8HOL 64 _ s.memory s.memaddrs
        (fun a=>Classical.propDecidable (s.memaddrs a)) s.be address (BitVec.ofNat 8 word.toNat) with
       | none=>
        rw [memoryRun] at run
        exact False.elim (valid (Prod.mk.inj run).1.symm)
       | some memory=>
        rw [memoryRun] at run
        have wide:=@mem_store_byte_source_domain_extend s.memory memory s.memaddrs domain
         (fun a=>Classical.propDecidable (s.memaddrs a)) (fun a=>Classical.propDecidable (domain a))
         subset s.be address (BitVec.ofNat 8 word.toNat) memoryRun
        rw [wide]
        cases run
        rfl
     | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
     | nStruct name fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
  | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
  | nStruct name fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)

/-- Domain extension preserves the actual successful 32 store and its exact memory. -/
theorem source_domain_transfer_store_32 (destination source : ExpHOL 64) :
 SourceDomainRunTransfer (.store32 destination source) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_store32] at run ⊢
 cases destinationRun : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) destination with
 | none=>
  rw [destinationRun] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some destinationValue=>
  rw [destinationRun] at run
  rw [eval_source_domain_extend s domain subset destination destinationValue destinationRun]
  cases destinationValue with
  | val payload=>
   cases payload with
   | word address=>
    dsimp only at run ⊢
    cases sourceRun : @evalHOLExact 64 F _ s.toExact
     (fun a=>Classical.propDecidable (s.memaddrs a)) source with
    | none=>
     rw [sourceRun] at run
     exact False.elim (valid (Prod.mk.inj run).1.symm)
    | some value=>
     rw [sourceRun] at run
     rw [eval_source_domain_extend s domain subset source value sourceRun]
     cases value with
     | val payload=>
      cases payload with
      | word word=>
       dsimp only at run ⊢
       cases memoryRun : @panMemStore32HOL 64 _ s.memory s.memaddrs
        (fun a=>Classical.propDecidable (s.memaddrs a)) s.be address (BitVec.ofNat 32 word.toNat) with
       | none=>
        rw [memoryRun] at run
        exact False.elim (valid (Prod.mk.inj run).1.symm)
       | some memory=>
        rw [memoryRun] at run
        have wide:=@mem_store32_source_domain_extend s.memory memory s.memaddrs domain
         (fun a=>Classical.propDecidable (s.memaddrs a)) (fun a=>Classical.propDecidable (domain a))
         subset s.be address (BitVec.ofNat 32 word.toNat) memoryRun
        rw [wide]
        cases run
        rfl
     | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
     | nStruct name fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
  | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
  | nStruct name fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)

#print axioms source_domain_transfer_store
#print axioms source_domain_transfer_store_byte
#print axioms source_domain_transfer_store_32
end InitECandidate.Runtime
