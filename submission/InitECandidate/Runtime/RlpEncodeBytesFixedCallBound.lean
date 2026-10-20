import InitECandidate.Runtime.RlpEncodeBytesCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem rlp_encode_bytes_wrong_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64)) (left right : ValueHOL 64) (length : BitVec 64)
 (code : s.code=originalRuntimeCode)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [left,right,.val (.word length)])
 (wrong : shapeEqHOL .one (shapeOfHOLExact left)=false ∨shapeEqHOL .one (shapeOfHOLExact right)=false) :
 evaluateHOLFiniteState s (.call (some (destination,none)) (ofString "rlp_encode_bytes") arguments)=(some .error,s) := by
 have lookup : lookupCodeHOLFinite s.code.lookup (ofString "rlp_encode_bytes") [left,right,.val (.word length)]=none := by
  rw [code,PanSemStateFiniteExact.lookupCodeHOLFinite_eq_none_iff]
  unfold Flapjack.lookupCodeHOLExact
  rw [originalRuntimeCode_rlpEncodeBytes_lookup]
  rcases wrong with bad|bad <;>simp [shapeOfHOLExact,shapeEqHOL,bad]
 rw [evaluateHOLFiniteState_call,args]
 dsimp only
 rw [lookup]

theorem ProgBounded.rlpEncodeBytesFixedCall (destination : Option (VarKind×MlS))
 (left right : ExpHOL 64) (length : BitVec 64) (small : length.toNat≤2^62) :
 ProgBounded (.call (some (destination,none)) (ofString "rlp_encode_bytes") [left,right,.const length])
  (rlpEncodeBytesSourceCost length.toNat+1) := by
 intro F s code budget
 cases leval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) left with
 | none=>
  have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [left,right,.const length]=none := by
   simp [evalListHOLFinite,evalListHOLExact,leval]
  rw [evaluateHOLFiniteState_call,args];simp
 | some lvalue=>
  cases reval : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) right with
  | none=>
   have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [left,right,.const length]=none := by
    simp [evalListHOLFinite,evalListHOLExact,leval,reval]
   rw [evaluateHOLFiniteState_call,args];simp
  | some rvalue=>
   have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [left,right,.const length]=
    some [lvalue,rvalue,.val (.word length)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,leval,reval]
   have invalid (wrong : shapeEqHOL .one (shapeOfHOLExact lvalue)=false ∨shapeEqHOL .one (shapeOfHOLExact rvalue)=false) :
    RunBounded s (.call (some (destination,none)) (ofString "rlp_encode_bytes") [left,right,.const length])
     (rlpEncodeBytesSourceCost length.toNat+1) := by
    have error:=rlp_encode_bytes_wrong_arguments s destination [left,right,.const length] lvalue rvalue length code args wrong
    unfold RunBounded;rw [error];simp
   cases lvalue with
   | rStruct fields=>exact invalid (Or.inl (by simp [shapeEqHOL,shapeOfHOLExact]))
   | nStruct name fields=>exact invalid (Or.inl (by simp [shapeEqHOL,shapeOfHOLExact]))
   | val lword=>
    cases lword with
    | word dst=>
     cases rvalue with
     | rStruct fields=>exact invalid (Or.inr (by simp [shapeEqHOL,shapeOfHOLExact]))
     | nStruct name fields=>exact invalid (Or.inr (by simp [shapeEqHOL,shapeOfHOLExact]))
     | val rword=>
      cases rword with
      | word src=>exact evaluate_rlp_encode_bytes_call_bounded s destination [left,right,.const length] dst src length args code small budget
#print axioms ProgBounded.rlpEncodeBytesFixedCall
end InitECandidate.Runtime
