import InitECandidate.Runtime.BuildMptIndexedEmptyPrefix
import InitECandidate.Runtime.RlpWordDeclarationReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def buildMptIndexedLoopBody : ProgHOL 64 :=
 match buildMptIndexedAt 3 with
 | .seq (.while _ body) _=>body
 | _=>.skip

def buildMptIndexedKeyTail : ProgHOL 64 :=statelessNext buildMptIndexedLoopBody

theorem source_build_mpt_indexed_key : buildMptIndexedLoopBody=
 .decCall (ofString "klen") .one (ofString "rlp_encode_word")
  [.var .global (ofString "mpt_key_scratch"),.var .local (ofString "i")] buildMptIndexedKeyTail := rfl

/-- At the actual indexed-trie insertion site, the declared key length is
between one and nine bytes. The original writer is executed with the real
global scratch pointer and loop index, and failures terminate within the
uniform source ceiling. -/
theorem build_mpt_indexed_key_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (pointer index : BitVec 64) (DF : Nat)
 (atScratch : s.globals.lookup (ofString "mpt_key_scratch")=some (.val (.word pointer)))
 (atIndex : s.locals.lookup (ofString "i")=some (.val (.word index)))
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (lower : 8≤pointer.toNat) (upper : pointer.toNat≤DF+8)
 (budget : rlpWriterSourceCost+1≤s.clock) :
 Reaches s buildMptIndexedLoopBody
  (fun next=>RlpWordDeclarationReady s next (ofString "klen") pointer DF)
  (rlpWriterSourceCost+1) buildMptIndexedKeyTail := by
 rw [source_build_mpt_indexed_key]
 apply rlp_word_declaration_reaches s (ofString "klen") _ buildMptIndexedKeyTail pointer index DF
  _ code fence cap lower upper budget
 simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atScratch,atIndex]

#print axioms source_build_mpt_indexed_key
#print axioms build_mpt_indexed_key_reaches
end InitECandidate.Runtime
