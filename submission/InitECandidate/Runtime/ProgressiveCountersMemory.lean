import InitECandidate.Runtime.ProgressiveLoopsMemory
import InitECandidate.Runtime.ProgressiveCounterDeclarationsBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressiveCounters_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes p n roots heap acc out mark watched : BitVec 64) (value : ValueHOL 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (atAcc : state.locals.lookup (ofString "acc") = some (.val (.word acc)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (accAligned : acc.toNat % 8 = 0) (accFits : acc.toNat + 32 ≤ 33806089496)
    (accBefore : watched.toNat < acc.toNat)
    (outAligned : out.toNat % 8 = 0) (outFits : out.toNat + 32 ≤ 33806089496)
    (outOutside : watched.toNat < out.toNat ∨ out.toNat + 32 ≤ watched.toNat)
    (small : n.toNat ≤ 134217712)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + 768 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : progressiveLoopsCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (progressiveAt 3) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_progressive_counters] at run
  obtain ⟨vk,innerK,evalK,runK,mK,_,_,_⟩ := dec_returned_state run
  rw [eval_const_word state 0] at evalK
  cases evalK
  obtain ⟨vo,innerO,evalO,runO,mO,_,_,_⟩ := dec_returned_state runK
  rw [eval_const_word _ 0] at evalO
  cases evalO
  obtain ⟨vs,innerS,evalS,runS,mS,_,_,_⟩ := dec_returned_state runO
  rw [eval_const_word _ 1] at evalS
  cases evalS
  let entered := setVarHOLFinite (ofString "size") (.val (.word (1#64)))
    (setVarHOLFinite (ofString "off") (.val (.word (0#64)))
      (setVarHOLFinite (ofString "k") (.val (.word (0#64))) state))
  have keep (key : MlS) (n1 : key ≠ ofString "size") (n2 : key ≠ ofString "off") (n3 : key ≠ ofString "k") :
      entered.locals.lookup key = state.locals.lookup key := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm n1,Ne.symm n2,Ne.symm n3]
  have enough : (n.toNat - (0#64).toNat) * (merkleBodyCost + 2) + (16 + (progressiveFoldCost + 16)) ≤ entered.clock := by
    have mono := Nat.mul_le_mul_right (merkleBodyCost + 2) small
    change _ ≤ state.clock
    clear run runK runO runS
    unfold progressiveLoopsCost at budget
    simp only [BitVec.toNat_ofNat,Nat.zero_mod,Nat.sub_zero]
    omega
  have frame := progressiveLoops_returned_memory entered innerS pointer accelerator zeroHashes p n 0 1 roots 0 heap acc out mark watched value
    atPointer atAccel atZero ((keep _ (by decide) (by decide) (by decide)).trans hp)
    (by simp (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((keep _ (by decide) (by decide) (by decide)).trans hn)
    (by simp (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((keep _ (by decide) (by decide) (by decide)).trans hr)
    (by simp (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) hh
    ((keep _ (by decide) (by decide) (by decide)).trans atAcc)
    ((keep _ (by decide) (by decide) (by decide)).trans atOut)
    ((keep _ (by decide) (by decide) (by decide)).trans atMark)
    accAligned accFits accBefore outAligned outFits outOutside small (progressive_power_counters_initial n)
    rootsAligned rootsFits rootsBefore heapAligned heapFits heapBefore accelAligned accelFits pointerFits
    accelOutside pointerOutside code enough runS
  rw [mK,mO,mS]
  exact frame

#print axioms progressiveCounters_returned_memory
end InitECandidate.Runtime
