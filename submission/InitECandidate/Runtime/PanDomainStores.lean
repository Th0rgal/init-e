import InitECandidate.Runtime.PanDomainAtoms
import InitECandidate.Runtime.PanDomainMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem panDomainMono_store {F : Type} (s : PanSemStateFiniteExact 64 F) (destination source : ExpHOL 64) : PanDomainMonoAt (.store destination source) s := by
  classical
  intro domain subset valid
  simp only [evaluateHOLFiniteState_store] at valid ⊢
  cases dest : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) destination with
  | none => simp only [evalHOLFinite_eq_toExact] at dest;simp [dest] at valid
  | some target => cases target with
    | rStruct fields => simp only [evalHOLFinite_eq_toExact] at dest;simp [dest] at valid
    | nStruct name fields => simp only [evalHOLFinite_eq_toExact] at dest;simp [dest] at valid
    | val payload => cases payload with
      | word address =>
        have nextDest := evalHOLFinite_memaddrs_mono s domain subset destination (.val (.word address)) dest
        simp only [evalHOLFinite_eq_toExact] at dest nextDest
        simp only [dest] at valid ⊢
        simp only [nextDest]
        cases src : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) source with
        | none => simp only [evalHOLFinite_eq_toExact] at src;simp [src] at valid
        | some value =>
          have nextSource := evalHOLFinite_memaddrs_mono s domain subset source value src
          simp only [evalHOLFinite_eq_toExact] at src nextSource
          simp only [src] at valid ⊢
          simp only [nextSource]
          cases store : @panMemStoresHOL 64 _ address (flattenHOL value) s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.memory with
          | none => rw [store] at valid;exact False.elim (valid rfl)
          | some memory =>
            have nextStore := @panMemStoresHOL_memaddrs_mono 64 _ s.memaddrs domain (fun a=>Classical.propDecidable (s.memaddrs a)) (fun a=>Classical.propDecidable (domain a)) subset (flattenHOL value) address s.memory memory store
            simp only [store,nextStore]

#print axioms panDomainMono_store
 theorem panDomainMono_store32 {F : Type} (s : PanSemStateFiniteExact 64 F) (destination source : ExpHOL 64) : PanDomainMonoAt (.store32 destination source) s := by
  classical
  intro domain subset valid
  simp only [evaluateHOLFiniteState_store32] at valid ⊢
  cases dest : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) destination with
  | none => simp only [evalHOLFinite_eq_toExact] at dest;simp [dest] at valid
  | some target => cases target with
    | rStruct fields => simp only [evalHOLFinite_eq_toExact] at dest;simp [dest] at valid
    | nStruct name fields => simp only [evalHOLFinite_eq_toExact] at dest;simp [dest] at valid
    | val payload => cases payload with
      | word address =>
        have nextDest := evalHOLFinite_memaddrs_mono s domain subset destination (.val (.word address)) dest
        simp only [evalHOLFinite_eq_toExact] at dest nextDest
        simp only [dest] at valid ⊢
        simp only [nextDest]
        cases src : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) source with
        | none => simp only [evalHOLFinite_eq_toExact] at src;simp [src] at valid
        | some value =>
          cases value with
          | rStruct fields => simp only [evalHOLFinite_eq_toExact] at src;simp [src] at valid
          | nStruct name fields => simp only [evalHOLFinite_eq_toExact] at src;simp [src] at valid
          | val payload => cases payload with
            | word value =>
              have nextSource := evalHOLFinite_memaddrs_mono s domain subset source (.val (.word value)) src
              simp only [evalHOLFinite_eq_toExact] at src nextSource
              simp only [src] at valid ⊢
              simp only [nextSource]
              cases store : @panMemStore32HOL 64 _ s.memory s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.be address (BitVec.ofNat 32 value.toNat) with
              | none => rw [store] at valid;exact False.elim (valid rfl)
              | some memory =>
                have nextStore := @panMemStore32HOL_memaddrs_mono 64 _ s.memory memory s.memaddrs domain (fun a=>Classical.propDecidable (s.memaddrs a)) (fun a=>Classical.propDecidable (domain a)) subset s.be address (BitVec.ofNat 32 value.toNat) store
                simp only [store,nextStore]

#print axioms panDomainMono_store32
 theorem panDomainMono_storeByte {F : Type} (s : PanSemStateFiniteExact 64 F) (destination source : ExpHOL 64) : PanDomainMonoAt (.storeByte destination source) s := by
  classical
  intro domain subset valid
  simp only [evaluateHOLFiniteState_storeByte] at valid ⊢
  cases dest : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) destination with
  | none => simp only [evalHOLFinite_eq_toExact] at dest;simp [dest] at valid
  | some target => cases target with
    | rStruct fields => simp only [evalHOLFinite_eq_toExact] at dest;simp [dest] at valid
    | nStruct name fields => simp only [evalHOLFinite_eq_toExact] at dest;simp [dest] at valid
    | val payload => cases payload with
      | word address =>
        have nextDest := evalHOLFinite_memaddrs_mono s domain subset destination (.val (.word address)) dest
        simp only [evalHOLFinite_eq_toExact] at dest nextDest
        simp only [dest] at valid ⊢
        simp only [nextDest]
        cases src : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) source with
        | none => simp only [evalHOLFinite_eq_toExact] at src;simp [src] at valid
        | some value =>
          cases value with
          | rStruct fields => simp only [evalHOLFinite_eq_toExact] at src;simp [src] at valid
          | nStruct name fields => simp only [evalHOLFinite_eq_toExact] at src;simp [src] at valid
          | val payload => cases payload with
            | word value =>
              have nextSource := evalHOLFinite_memaddrs_mono s domain subset source (.val (.word value)) src
              simp only [evalHOLFinite_eq_toExact] at src nextSource
              simp only [src] at valid ⊢
              simp only [nextSource]
              cases store : @panMemStoreByteWord8HOL 64 _ s.memory s.memaddrs (fun a=>Classical.propDecidable (s.memaddrs a)) s.be address (BitVec.ofNat 8 value.toNat) with
              | none => rw [store] at valid;exact False.elim (valid rfl)
              | some memory =>
                have nextStore := @panMemStoreByteWord8HOL_memaddrs_mono 64 _ s.memory memory s.memaddrs domain (fun a=>Classical.propDecidable (s.memaddrs a)) (fun a=>Classical.propDecidable (domain a)) subset s.be address (BitVec.ofNat 8 value.toNat) store
                simp only [store,nextStore]

#print axioms panDomainMono_storeByte
end InitECandidate.Runtime
