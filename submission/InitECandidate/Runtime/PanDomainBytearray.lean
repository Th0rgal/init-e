import InitECandidate.Runtime.PanDomainExpression
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 theorem panMemLoadByteWord8HOL_memaddrs_mono {width : Nat} [NeZero width]
    (memory : BitVec width→HolWordLab width) (source target : BitVec width→Prop)
    [DecidablePred source] [DecidablePred target] (be : Bool) (address : BitVec width) (byte : BitVec 8)
    (subset : ∀ address, source address→target address)
    (run : panMemLoadByteWord8HOL memory source be address=some byte) :
    panMemLoadByteWord8HOL memory target be address=some byte := by
  unfold panMemLoadByteWord8HOL at run ⊢
  cases cell : memory (panByteAlignHOL address) with
  | word value =>
    by_cases domain : source (panByteAlignHOL address)
    · simpa only [cell,if_pos domain,if_pos (subset _ domain)] using run
    · simp [cell,domain] at run
 theorem readBytearrayWordHOL_mono {width : Nat} [NeZero width]
    (source target : BitVec width→Option (BitVec 8))
    (preserve : ∀ address byte,source address=some byte→target address=some byte)
    (length : Nat) (address : BitVec width) (bytes : List (BitVec 8))
    (run : readBytearrayWordHOL address length source=some bytes) :
    readBytearrayWordHOL address length target=some bytes := by
  induction length generalizing address bytes with
  | zero => simpa [readBytearrayWordHOL] using run
  | succ length ih =>
    simp only [readBytearrayWordHOL] at run ⊢
    cases first : source address with
    | none => simp only [first,Option.bind_none,reduceCtorEq] at run; cases run
    | some byte =>
      rw [preserve address byte first]
      cases rest : readBytearrayWordHOL (address + 1) length source with
      | none => simp only [first,rest,Option.bind_some,Option.bind_none,reduceCtorEq] at run; cases run
      | some tail => rw [ih (address + 1) tail rest];simpa only [first,rest,Option.bind_some] using run
 theorem panWriteBytearrayWord8HOL_memaddrs_mono {width : Nat} [NeZero width]
    (memory : BitVec width→HolWordLab width) (source target : BitVec width→Prop)
    [DecidablePred source] [DecidablePred target] (be : Bool)
    (subset : ∀ address,source address→target address)
    (bytes : List (BitVec 8)) (address : BitVec width) (oldBytes : List (BitVec 8))
    (readable : readBytearrayWordHOL address bytes.length (panMemLoadByteWord8HOL memory source be)=some oldBytes) :
    panWriteBytearrayWord8HOL address bytes memory source be=panWriteBytearrayWord8HOL address bytes memory target be := by
  induction bytes generalizing address oldBytes with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [List.length_cons,readBytearrayWordHOL] at readable
    cases first : panMemLoadByteWord8HOL memory source be address with
    | none => simp only [first,Option.bind_none,reduceCtorEq] at readable; cases readable
    | some oldByte =>
      cases rest : readBytearrayWordHOL (address + 1) bytes.length (panMemLoadByteWord8HOL memory source be) with
      | none => simp only [first,rest,Option.bind_some,Option.bind_none,reduceCtorEq] at readable; cases readable
      | some tail =>
        have tails := ih (address + 1) tail rest
        have dom : source (panByteAlignHOL address) := by
          unfold panMemLoadByteWord8HOL at first
          cases cell : memory (panByteAlignHOL address) with
          | word value =>
            by_cases hd : source (panByteAlignHOL address)
            · exact hd
            · simp [cell,hd] at first
        simp only [panWriteBytearrayWord8HOL,tails]
        unfold panMemStoreByteWord8HOL
        cases value : (panWriteBytearrayWord8HOL (address + 1) bytes memory target be) (panByteAlignHOL address) with
        | word cell => simp only [if_pos dom,if_pos (subset _ dom)]
#print axioms panMemLoadByteWord8HOL_memaddrs_mono
#print axioms readBytearrayWordHOL_mono
#print axioms panWriteBytearrayWord8HOL_memaddrs_mono
end InitECandidate.Runtime
