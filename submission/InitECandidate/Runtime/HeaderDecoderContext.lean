import InitECandidate.Runtime.DecodeHeaderFinalSuffixBound
import InitECandidate.Runtime.HeaderWordFieldChainReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Fixed geometry and accepted field count obtained before field parsing. -/
structure HeaderDecoderGeometry (array count inputLength scratch frame record flag : BitVec 64)
    (ceiling inputLimit : Nat) : Prop where
  before : array.toNat + count.toNat * 16 ≤ record.toNat
  recordFits : record.toNat + 248 < 2^64
  above : ceiling ≤ array.toNat
  fits : array.toNat + count.toNat * 16 ≤ 2^64
  inputBound : inputLength.toNat ≤ inputLimit
  limitBound : inputLimit + 9 < 2^64
  orderedFrame : frame ≤ scratch
  framePositive : 0 < frame.toNat
  scratchBelow : scratch.toNat ≤ ceiling
  accepted : (count = 21 ∧ flag = 0) ∨ (count = 23 ∧ flag = 1)

/-- The actual locals, readable table and parser workspace used between fields. -/
structure HeaderDecoderContext {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame record flag : BitVec 64) (ceiling : Nat) : Prop where
  atArray : s.locals.lookup (ofString "arr") = some (.val (.word array))
  atRecord : s.locals.lookup (ofString "h") = some (.val (.word record))
  atFlag : s.locals.lookup (ofString "is_current") = some (.val (.word flag))
  table : RlpSliceInputPrefix s array input inputLength count.toNat
  scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch))
  frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame))
  code : s.code = originalRuntimeCode
  arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address

theorem HeaderDecoderGeometry.countBound {array count inputLength scratch frame record flag : BitVec 64}
    {ceiling inputLimit : Nat} (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit) :
    21 ≤ count.toNat := by
  rcases g.accepted with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide

theorem HeaderDecoderGeometry.currentCount {array count inputLength scratch frame record flag : BitVec 64}
    {ceiling inputLimit : Nat} (g : HeaderDecoderGeometry array count inputLength scratch frame record flag ceiling inputLimit)
    (nonzero : flag ≠ 0) : 23 ≤ count.toNat := by
  rcases g.accepted with ⟨_,rfl⟩ | ⟨rfl,_⟩
  · exact False.elim (nonzero rfl)
  · decide

theorem HeaderDecoderContext.after_frame {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {array count input inputLength scratch frame record flag : BitVec 64} {ceiling : Nat}
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (table : RlpSliceInputPrefix post array input inputLength count.toNat)
    (locals : ∀ name, name = ofString "arr" ∨ name = ofString "h" ∨ name = ofString "is_current" →
      post.locals.lookup name = s.locals.lookup name)
    (domain : post.memaddrs = s.memaddrs) (code : post.code = s.code)
    (globals : ∀ name : MlS, post.globals.lookup name = s.globals.lookup name) :
    HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling := by
  refine ⟨?_,?_,?_,table,?_,?_,code.trans c.code,?_⟩
  · rw [locals _ (Or.inl rfl)]; exact c.atArray
  · rw [locals _ (Or.inr (Or.inl rfl))]; exact c.atRecord
  · rw [locals _ (Or.inr (Or.inr rfl))]; exact c.atFlag
  · rw [globals]; exact c.scratchGlobal
  · rw [globals]; exact c.frameGlobal
  · intro address lo hi
    rw [domain]
    exact c.arena address lo hi

theorem HeaderDecoderContext.after_update {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {array count input inputLength scratch frame record flag : BitVec 64} {ceiling : Nat}
    (c : HeaderDecoderContext s array count input inputLength scratch frame record flag ceiling)
    (name : MlS) (value : ValueHOL 64)
    (different : name ≠ ofString "arr" ∧ name ≠ ofString "h" ∧ name ≠ ofString "is_current")
    (locals : post.locals = s.locals.update (name,value))
    (table : RlpSliceInputPrefix post array input inputLength count.toNat)
    (domain : post.memaddrs = s.memaddrs) (code : post.code = s.code)
    (globals : ∀ global : MlS, post.globals.lookup global = s.globals.lookup global) :
    HeaderDecoderContext post array count input inputLength scratch frame record flag ceiling := by
  apply c.after_frame table ?_ domain code globals
  intro key important
  rw [locals]
  rcases important with rfl | rfl | rfl
  all_goals simp [HolFiniteMapExact.lookup_update,FUPDATE,different.1,different.2.1,different.2.2,Ne.symm different.1,Ne.symm different.2.1,Ne.symm different.2.2]

#print axioms HeaderDecoderGeometry.countBound
#print axioms HeaderDecoderGeometry.currentCount
#print axioms HeaderDecoderContext.after_frame
#print axioms HeaderDecoderContext.after_update
end InitECandidate.Runtime
