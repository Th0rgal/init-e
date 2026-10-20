import InitECandidate.Runtime.SourceDomainProgramTransfer
import Flapjack.Pancake.Semantics.PanSem.ShMemExact
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Shared-load checks and FFI effects do not inspect the ordinary domain.
The shared predicate itself is kept unchanged. -/
theorem shared_load_ordinary_domain_update {F : Type} (s : PanSemStateFiniteExact 64 F)
 (domain : BitVec 64→Prop) (kind : VarKind) (name : MlS) (address : BitVec 64) (nb : Nat) :
 @shMemLoadHOLFiniteExact 64 F _ {s with memaddrs:=domain}
  (fun a=>Classical.propDecidable (s.shMemaddrs a)) kind name address nb=
 (let output:=@shMemLoadHOLFiniteExact 64 F _ s
   (fun a=>Classical.propDecidable (s.shMemaddrs a)) kind name address nb;
  (output.1,{output.2 with memaddrs:=domain})) := by
 unfold shMemLoadHOLFiniteExact
 by_cases zero : nb=0
 · simp only [if_pos zero]
   by_cases accessible : s.shMemaddrs address
   · simp only [show ({s with memaddrs:=domain}).shMemaddrs=s.shMemaddrs from rfl,if_pos accessible]
     cases outcome : callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
      (panWordToBytesHOL address false) <;>cases kind <;>rfl
   · simp only [show ({s with memaddrs:=domain}).shMemaddrs=s.shMemaddrs from rfl,if_neg accessible]
 · simp only [if_neg zero]
   by_cases accessible : s.shMemaddrs (panByteAlignHOL address)
   · simp only [show ({s with memaddrs:=domain}).shMemaddrs=s.shMemaddrs from rfl,if_pos accessible]
     cases outcome : callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
      (panWordToBytesHOL address false) <;>cases kind <;>rfl
   · simp only [show ({s with memaddrs:=domain}).shMemaddrs=s.shMemaddrs from rfl,if_neg accessible]

/-- The full shared-memory load transfers its actual address expression and
checked destination, keeping the shared FFI operation and final state identical. -/
theorem source_domain_transfer_shared_load (operator : OpSize) (kind : VarKind) (name : MlS)
 (expression : ExpHOL 64) : SourceDomainRunTransfer (.shMemLoad operator kind name expression) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_shMemLoad_source,evalHOLFinite_eq_toExact] at run ⊢
 cases actual : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) expression with
 | none=>
  rw [actual] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some value=>
  rw [actual] at run
  rw [eval_source_domain_extend s domain subset expression value actual]
  cases value with
  | val payload=>
   cases payload with
   | word address=>
    dsimp only at run ⊢
    have lookupSame : lookupKvarHOLFinite kind name {s with memaddrs:=domain}=lookupKvarHOLFinite kind name s := by
     cases kind <;>rfl
    rw [lookupSame]
    cases binding : lookupKvarHOLFinite kind name s with
    | none=>
     rw [binding] at run
     exact False.elim (valid (Prod.mk.inj run).1.symm)
    | some old=>
     rw [binding] at run
     cases old with
     | val payload=>
      cases payload with
      | word oldWord=>
       dsimp only at run ⊢
       rw [shared_load_ordinary_domain_update]
       cases outcome : @shMemLoadHOLFiniteExact 64 F _ s
        (fun a=>Classical.propDecidable (s.shMemaddrs a)) kind name address (nbOpHOL operator) with
       | mk output middle=>
        rw [outcome] at run
        cases run
        rfl
     | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
     | nStruct structName fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
  | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
  | nStruct structName fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)

#print axioms shared_load_ordinary_domain_update
#print axioms source_domain_transfer_shared_load

/-- Finite repacking of the exact shared-store helper used by the source clause. -/
noncomputable def sourceSharedStoreResult {F : Type} (s : PanSemStateFiniteExact 64 F)
 (word address : BitVec 64) (nb : Nat) :
 Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F := by
 classical
 let output:=shMemStoreHOLExact s.toExact word address nb
 exact (output.1,ofExact output.2 (shMemStoreHOLExact_finiteSupport s.toExact word address nb s.toExact_finiteSupport))


/-- The canonical finite carrier codec is injective; its finite-support
witnesses are proofs and do not alter the source state. -/
theorem source_state_toExact_injective {F : Type} :
 Function.Injective (PanSemStateFiniteExact.toExact (width:=64) (σ:=F)) := by
 intro left right equal
 have same : ofExact left.toExact left.toExact_finiteSupport=ofExact right.toExact right.toExact_finiteSupport := by
  congr 1
 simpa only [ofExact_toExact] using same

/-- Shared stores on the broad source state do not inspect ordinary memory. -/
theorem shared_store_exact_domain_update {F : Type} (s : PanSemStateExact 64 F)
 (domain : BitVec 64→Prop) (word address : BitVec 64) (nb : Nat) :
 @shMemStoreHOLExact 64 F _ {s with memaddrs:=domain}
  (fun a=>Classical.propDecidable (s.shMemaddrs a)) word address nb=
 (let output:=@shMemStoreHOLExact 64 F _ s
   (fun a=>Classical.propDecidable (s.shMemaddrs a)) word address nb;
  (output.1,{output.2 with memaddrs:=domain})) := by
 unfold shMemStoreHOLExact
 by_cases zero : nb=0
 · simp only [if_pos zero]
   by_cases accessible : s.shMemaddrs address
   · simp only [show ({s with memaddrs:=domain}).shMemaddrs=s.shMemaddrs from rfl,if_pos accessible]
     cases outcome : callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
      (panWordToBytesHOL word false++panWordToBytesHOL address false) <;>rfl
   · simp only [show ({s with memaddrs:=domain}).shMemaddrs=s.shMemaddrs from rfl,if_neg accessible]
 · simp only [if_neg zero]
   by_cases accessible : s.shMemaddrs (panByteAlignHOL address)
   · simp only [show ({s with memaddrs:=domain}).shMemaddrs=s.shMemaddrs from rfl,if_pos accessible]
     cases outcome : callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
      ((panWordToBytesHOL word false).take nb++panWordToBytesHOL address false) <;>rfl
   · simp only [show ({s with memaddrs:=domain}).shMemaddrs=s.shMemaddrs from rfl,if_neg accessible]

/-- Repacking the exact shared-store result retains that same commutation. -/
theorem shared_store_ordinary_domain_update {F : Type} (s : PanSemStateFiniteExact 64 F)
 (domain : BitVec 64→Prop) (word address : BitVec 64) (nb : Nat) :
 sourceSharedStoreResult {s with memaddrs:=domain} word address nb=
 (let output:=sourceSharedStoreResult s word address nb;
  (output.1,{output.2 with memaddrs:=domain})) := by
 have broad:=shared_store_exact_domain_update s.toExact domain word address nb
 have first:=congrArg (fun pair : Option (PanSemResultExact 64) × PanSemStateExact 64 F=>pair.1) broad
 have second:=congrArg (fun pair : Option (PanSemResultExact 64) × PanSemStateExact 64 F=>pair.2) broad
 apply Prod.ext
 · exact first
 · apply source_state_toExact_injective
   simp only [sourceSharedStoreResult,toExact_ofExact]
   exact second

#print axioms source_state_toExact_injective
#print axioms shared_store_exact_domain_update
#print axioms shared_store_ordinary_domain_update

/-- The full shared-memory store transfers its actual address and value,
keeping the shared predicate, host operation and FFI trace unchanged. -/
theorem source_domain_transfer_shared_store (operator : OpSize) (destination source : ExpHOL 64) :
 SourceDomainRunTransfer (.shMemStore operator destination source) := by
 intro F s domain subset result post run valid
 rw [evaluateHOLFiniteState_shMemStore_total] at run ⊢
 dsimp only at run ⊢
 cases destinationRun : @evalHOLExact 64 F _ s.toExact
  (fun a=>Classical.propDecidable (s.memaddrs a)) destination with
 | none=>
  rw [destinationRun] at run
  exact False.elim (valid (Prod.mk.inj run).1.symm)
 | some destinationValue=>
  rw [destinationRun] at run
  rw [eval_source_domain_extend s domain subset destination destinationValue destinationRun]
  cases sourceRun : @evalHOLExact 64 F _ s.toExact
   (fun a=>Classical.propDecidable (s.memaddrs a)) source with
  | none=>
   rw [sourceRun] at run
   cases destinationValue <;>exact False.elim (valid (Prod.mk.inj run).1.symm)
  | some value=>
   rw [sourceRun] at run
   rw [eval_source_domain_extend s domain subset source value sourceRun]
   cases destinationValue with
   | val payload=>
    cases payload with
    | word address=>
     cases value with
     | val payload=>
      cases payload with
      | word word=>
       change sourceSharedStoreResult s word address (nbOpHOL operator)=(result,post) at run
       change sourceSharedStoreResult {s with memaddrs:=domain} word address (nbOpHOL operator)=
        (result,{post with memaddrs:=domain})
       rw [shared_store_ordinary_domain_update,run]
     | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
     | nStruct name fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
   | rStruct fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)
   | nStruct name fields=>exact False.elim (valid (Prod.mk.inj run).1.symm)

#print axioms source_domain_transfer_shared_store
end InitECandidate.Runtime
