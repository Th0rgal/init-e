import InitECandidate.Runtime.PanDomainAtoms
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem finiteState_eq_of_fields {F : Type} (s t : PanSemStateFiniteExact 64 F)
    (h_locals : s.locals=t.locals)
    (h_globals : s.globals=t.globals)
    (h_structs : s.structs=t.structs)
    (h_code : s.code=t.code)
    (h_eshapes : s.eshapes=t.eshapes)
    (h_memory : s.memory=t.memory)
    (h_memaddrs : s.memaddrs=t.memaddrs)
    (h_shMemaddrs : s.shMemaddrs=t.shMemaddrs)
    (h_clock : s.clock=t.clock)
    (h_be : s.be=t.be)
    (h_ffi : s.ffi=t.ffi)
    (h_baseAddr : s.baseAddr=t.baseAddr)
    (h_topAddr : s.topAddr=t.topAddr)
    : s=t := by
  cases s
  cases t
  simp_all
 theorem shMemLoadHOLFiniteExact_memaddrs {F : Type} (s : PanSemStateFiniteExact 64 F) (domain : BitVec 64→Prop) (kind : VarKind) (name : MlS) (address : BitVec 64) (nb : Nat) :
    @shMemLoadHOLFiniteExact 64 F _ {s with memaddrs:=domain} (fun a=>Classical.propDecidable (s.shMemaddrs a)) kind name address nb=
      ((@shMemLoadHOLFiniteExact 64 F _ s (fun a=>Classical.propDecidable (s.shMemaddrs a)) kind name address nb).1,
      {(@shMemLoadHOLFiniteExact 64 F _ s (fun a=>Classical.propDecidable (s.shMemaddrs a)) kind name address nb).2 with memaddrs:=domain}) := by
  classical
  unfold shMemLoadHOLFiniteExact
  by_cases zero : nb=0
  · simp only [zero,if_pos]
    by_cases accessible : s.shMemaddrs address
    · simp only [if_pos accessible]
      cases callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 0] (panWordToBytesHOL address false) <;>cases kind <;>rfl
    · simp only [if_neg accessible]
  · simp only [if_neg zero]
    by_cases accessible : s.shMemaddrs (panByteAlignHOL address)
    · simp only [if_pos accessible]
      cases callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb] (panWordToBytesHOL address false) <;>cases kind <;>rfl
    · simp only [if_neg accessible]
 theorem panDomainMono_shMemLoad {F : Type} (s : PanSemStateFiniteExact 64 F) (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL 64) : PanDomainMonoAt (.shMemLoad operator kind name address) s := by
  classical
  intro domain subset valid
  simp only [evaluateHOLFiniteState_shMemLoad_source] at valid ⊢
  cases old : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) address with
  | none => simp only [old] at valid;exact False.elim (valid rfl)
  | some value => cases value with
    | rStruct fields => simp only [old] at valid;exact False.elim (valid rfl)
    | nStruct name fields => simp only [old] at valid;exact False.elim (valid rfl)
    | val payload => cases payload with
      | word pointer =>
        have next:=evalHOLFinite_memaddrs_mono s domain subset address (.val (.word pointer)) old
        simp only [old] at valid ⊢
        simp only [next]
        have lookupEq : lookupKvarHOLFinite kind name {s with memaddrs:=domain}=lookupKvarHOLFinite kind name s := by cases kind <;>rfl
        simp only [lookupEq]
        cases lookup : lookupKvarHOLFinite kind name s with
        | none => simp only [lookup] at valid;exact False.elim (valid rfl)
        | some value => cases value with
          | rStruct fields => simp only [lookup] at valid;exact False.elim (valid rfl)
          | nStruct name fields => simp only [lookup] at valid;exact False.elim (valid rfl)
          | val payload => cases payload with
            | word previous =>
              simp only [lookup,shMemLoadHOLFiniteExact_memaddrs]
 theorem panDomainMono_shMemStore {F : Type} (s : PanSemStateFiniteExact 64 F) (operator : OpSize) (address value : ExpHOL 64) : PanDomainMonoAt (.shMemStore operator address value) s := by
  classical
  intro domain subset valid
  simp only [evaluateHOLFiniteState_shMemStore_total] at valid ⊢
  cases dest : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) address with
  | none => simp only [evalHOLFinite_eq_toExact] at dest;simp only [dest] at valid;exact False.elim (valid rfl)
  | some target => cases target with
    | rStruct fields => simp only [evalHOLFinite_eq_toExact] at dest;simp only [dest] at valid;exact False.elim (valid rfl)
    | nStruct name fields => simp only [evalHOLFinite_eq_toExact] at dest;simp only [dest] at valid;exact False.elim (valid rfl)
    | val payload => cases payload with
      | word pointer =>
        have nextDest:=evalHOLFinite_memaddrs_mono s domain subset address (.val (.word pointer)) dest
        simp only [evalHOLFinite_eq_toExact] at dest nextDest
        simp only [dest] at valid ⊢
        simp only [nextDest]
        cases src : @evalHOLFinite 64 F _ s (fun a=>Classical.propDecidable (s.memaddrs a)) value with
        | none => simp only [evalHOLFinite_eq_toExact] at src;simp only [src] at valid;exact False.elim (valid rfl)
        | some source => cases source with
          | rStruct fields => simp only [evalHOLFinite_eq_toExact] at src;simp only [src] at valid;exact False.elim (valid rfl)
          | nStruct name fields => simp only [evalHOLFinite_eq_toExact] at src;simp only [src] at valid;exact False.elim (valid rfl)
          | val payload => cases payload with
            | word word =>
              have nextSource:=evalHOLFinite_memaddrs_mono s domain subset value (.val (.word word)) src
              simp only [evalHOLFinite_eq_toExact] at src nextSource
              simp only [src] at valid ⊢
              simp only [nextSource]
              apply Prod.ext
              · simp only [Prod.fst,toExact]
                unfold shMemStoreHOLExact
                by_cases zero : nbOpHOL operator=0
                · simp only [zero,if_pos]
                  by_cases accessible : s.shMemaddrs pointer
                  · simp only [if_pos accessible]
                    cases callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 0] (panWordToBytesHOL word false ++panWordToBytesHOL pointer false) <;>rfl
                  · simp only [if_neg accessible]
                · simp only [if_neg zero]
                  by_cases accessible : s.shMemaddrs (panByteAlignHOL pointer)
                  · simp only [if_pos accessible]
                    cases callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 (nbOpHOL operator)] ((panWordToBytesHOL word false).take (nbOpHOL operator) ++panWordToBytesHOL pointer false) <;>rfl
                  · simp only [if_neg accessible]
              · apply finiteState_eq_of_fields
                all_goals try (apply HolFiniteMapExact.ext; funext key)
                all_goals simp only [Prod.snd,ofExact,toExact]
                all_goals
                  unfold shMemStoreHOLExact
                  by_cases zero : nbOpHOL operator=0
                  · simp only [zero,if_pos]
                    by_cases accessible : s.shMemaddrs pointer
                    · simp only [if_pos accessible]
                      cases callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 0] (panWordToBytesHOL word false ++panWordToBytesHOL pointer false) <;>rfl
                    · simp only [if_neg accessible]
                  · simp only [if_neg zero]
                    by_cases accessible : s.shMemaddrs (panByteAlignHOL pointer)
                    · simp only [if_pos accessible]
                      cases callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 (nbOpHOL operator)] ((panWordToBytesHOL word false).take (nbOpHOL operator) ++panWordToBytesHOL pointer false) <;>rfl
                    · simp only [if_neg accessible]
#print axioms finiteState_eq_of_fields
#print axioms shMemLoadHOLFiniteExact_memaddrs
#print axioms panDomainMono_shMemLoad
#print axioms panDomainMono_shMemStore
end InitECandidate.Runtime
