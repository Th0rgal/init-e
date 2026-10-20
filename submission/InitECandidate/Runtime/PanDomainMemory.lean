import InitECandidate.Runtime.PanDomainExpression
namespace InitECandidate.Runtime
open Flapjack
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem panMemStoresHOL_memaddrs_mono {width : Nat} [NeZero width]
    (source target : BitVec width→Prop) [DecidablePred source] [DecidablePred target]
    (subset : ∀address,source address→target address) (values : List (HolWordLab width))
    (address : BitVec width) (memory next : BitVec width→HolWordLab width)
    (run : panMemStoresHOL address values source memory=some next) :
    panMemStoresHOL address values target memory=some next := by
  induction values generalizing address memory with
  | nil => exact run
  | cons value rest ih =>
    by_cases domain : source address
    · simp only [panMemStoresHOL,panMemStoreHOL,if_pos domain] at run
      simp only [panMemStoresHOL,panMemStoreHOL,if_pos (subset _ domain)]
      exact ih _ _ run
    · simp [panMemStoresHOL,panMemStoreHOL,domain] at run
 theorem panMemStore32HOL_memaddrs_mono {width : Nat} [NeZero width]
    (memory next : BitVec width→HolWordLab width) (source target : BitVec width→Prop)
    [DecidablePred source] [DecidablePred target] (subset : ∀address,source address→target address)
    (be : Bool) (address : BitVec width) (value : BitVec 32)
    (run : panMemStore32HOL memory source be address value=some next) :
    panMemStore32HOL memory target be address value=some next := by
  unfold panMemStore32HOL at run ⊢
  by_cases aligned : address.toNat%4=0
  · simp only [if_pos aligned] at run ⊢
    cases cell : memory (panByteAlignHOL address) with
    | word word =>
      by_cases domain : source (panByteAlignHOL address)
      · simpa only [cell,if_pos domain,if_pos (subset _ domain)] using run
      · simp [cell,domain] at run
  · simp [aligned] at run
 theorem panMemStoreByteHOL_memaddrs_mono {width : Nat} [NeZero width]
    (memory next : BitVec width→HolWordLab width) (source target : BitVec width→Prop)
    [DecidablePred source] [DecidablePred target] (subset : ∀address,source address→target address)
    (be : Bool) (address : BitVec width) (value : UInt8)
    (run : panMemStoreByteHOL memory source be address value=some next) :
    panMemStoreByteHOL memory target be address value=some next := by
  unfold panMemStoreByteHOL at run ⊢
  cases cell : memory (panByteAlignHOL address) with
  | word word =>
    by_cases domain : source (panByteAlignHOL address)
    · simpa only [cell,if_pos domain,if_pos (subset _ domain)] using run
    · simp [cell,domain] at run
 theorem panMemStoreByteWord8HOL_memaddrs_mono {width : Nat} [NeZero width]
    (memory next : BitVec width→HolWordLab width) (source target : BitVec width→Prop)
    [DecidablePred source] [DecidablePred target] (subset : ∀address,source address→target address)
    (be : Bool) (address : BitVec width) (value : BitVec 8)
    (run : panMemStoreByteWord8HOL memory source be address value=some next) :
    panMemStoreByteWord8HOL memory target be address value=some next := by
  unfold panMemStoreByteWord8HOL at run ⊢
  cases cell : memory (panByteAlignHOL address) with
  | word word =>
    by_cases domain : source (panByteAlignHOL address)
    · simpa only [cell,if_pos domain,if_pos (subset _ domain)] using run
    · simp [cell,domain] at run
#print axioms panMemStoreByteWord8HOL_memaddrs_mono
#print axioms panMemStoresHOL_memaddrs_mono
#print axioms panMemStore32HOL_memaddrs_mono
#print axioms panMemStoreByteHOL_memaddrs_mono
end InitECandidate.Runtime
