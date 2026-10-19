import InitECandidate.Runtime.HeaderBytesChainReach
import InitECandidate.Runtime.HeaderWordFieldChainReach
/-!
The uniform carry predicate used to chain the actual decoder phases.

`HeaderSuffixCarry s post …` says that a word sits at record offset 32 of `post`, that
the domain, the code and the globals of `post` agree with the reference state `s`, and
that the readable slice table and the `arr`/`h` locals are still in place.  Every phase
carrier of the header decoder establishes exactly this from the same predicate on its
entry state, so the phases compose by `reaches_trans_budget`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The state root word at record offset 32, with the decoder's working context. -/
def HeaderSuffixCarry {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array count input inputLength record word : BitVec 64) : Prop :=
  post.memory (record + 32#64) = .word word ∧
    post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
    (∀ global : MlS, post.globals.lookup global = s.globals.lookup global) ∧
    RlpSliceInputPrefix post array input inputLength count.toNat ∧
    post.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
    post.locals.lookup (ofString "h") = some (.val (.word record))

/-- Rebuild the carry predicate from the seven facts a phase produced. -/
theorem header_carry_intro {F : Type} (s next post : PanSemStateFiniteExact 64 F)
    (array count input inputLength record word : BitVec 64)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (rootMem : post.memory (record + 32#64) = .word word)
    (domain : post.memaddrs = next.memaddrs) (code : post.code = next.code)
    (globals : ∀ global : MlS, post.globals.lookup global = next.globals.lookup global)
    (table : RlpSliceInputPrefix post array input inputLength count.toNat)
    (atArray : post.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atRecord : post.locals.lookup (ofString "h") = some (.val (.word record))) :
    HeaderSuffixCarry s post array count input inputLength record word := by
  obtain ⟨_,carryDomain,carryCode,carryGlobals,_,_,_⟩ := carry
  refine ⟨rootMem,domain.trans carryDomain,code.trans carryCode,?_,table,atArray,atRecord⟩
  intro global
  exact (globals global).trans (carryGlobals global)

/-- The carry predicate survives a phase whose frame is a word-field chain frame. -/
theorem header_carry_of_word_frame {F : Type} (s next post : PanSemStateFiniteExact 64 F)
    (array count input inputLength record word : BitVec 64) (ceiling : Nat)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (facts : post.memory (record + 32#64) = .word word ∧
      HeaderWordFieldFrame next post array count input inputLength record ceiling) :
    HeaderSuffixCarry s post array count input inputLength record word := by
  obtain ⟨rootMem,frame⟩ := facts
  refine header_carry_intro s next post array count input inputLength record word carry rootMem
    frame.domain frame.code frame.globals frame.table ?_ ?_
  · rw [frame.locals (ofString "arr") (by decide)]
    exact carry.2.2.2.2.2.1
  · rw [frame.locals (ofString "h") (by decide)]
    exact carry.2.2.2.2.2.2

/-- The carry predicate survives a phase whose frame is a bytes-chain frame. -/
theorem header_carry_of_bytes_frame {F : Type} (s next post : PanSemStateFiniteExact 64 F)
    (array count input inputLength record word : BitVec 64) (ceiling : Nat)
    (carry : HeaderSuffixCarry s next array count input inputLength record word)
    (facts : post.memory (record + 32#64) = .word word ∧
      HeaderBytesFrame next post array count input inputLength record ceiling) :
    HeaderSuffixCarry s post array count input inputLength record word := by
  obtain ⟨rootMem,frame⟩ := facts
  refine header_carry_intro s next post array count input inputLength record word carry rootMem
    frame.domain frame.code frame.globals frame.table ?_ ?_
  · rw [frame.locals (ofString "arr") (by decide)]
    exact carry.2.2.2.2.2.1
  · rw [frame.locals (ofString "h") (by decide)]
    exact carry.2.2.2.2.2.2

#print axioms header_carry_intro
#print axioms header_carry_of_word_frame
#print axioms header_carry_of_bytes_frame
end InitECandidate.Runtime
