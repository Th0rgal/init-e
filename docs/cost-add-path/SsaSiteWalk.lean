import InitECandidate.Proofs.FrontendStages.Word.FunctionsFacts
import InitECandidate.Proofs.WordBackend.FunctionsFacts
import InitECandidate.Runtime.WordIselTransfer
import InitECandidate.Runtime.SourceSiteMoves
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target InitECandidate.Runtime.FineCost

def selCost (e : WordLangExpHOL (BitVec 64)) : Nat :=
  InitECandidate.Runtime.FineCost.iselCost (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e))

def refined (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match InitECandidate.Runtime.WordToStack.refinedWordStackLeafBudget p with
  | some b => b
  | none => match p with
    | .ite _ _ _ _ _ => 23
    | .loop _ _ _ => 2
    | .call none _ _ _ => 41
    | .call (some (values,_,_,_,_)) _ args handler =>
        (if handler.isSome then 189 else 63)+39*(args.length+1-22)+21*(values.length+1-22)
    | _ => 0

def optP (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match p with
  | .move _ pairs => 24 * pairs.length
  | .inst _ | .get _ _ | .locValue _ _ | .opCurrHeap _ _ _ => max 24 (refined p)
  | _ => refined p

def preP (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match p with
  | .assign _ e => selCost e
  | .set _ e => selCost e + 12
  | .store e _ => selCost e + 24
  | .shareInst _ _ e => selCost e + 13
  | p => optP p

partial def sb : WordLangExpHOL (BitVec 64) → Nat
  | .const _ | .var _ | .lookup _ => 24
  | .load a => sb a + 24
  | .shift _ a b => sb a + sb b + 28
  | .op _ [] => 24
  | .op _ as => (as.map sb).sum + 24 * (as.length - 1)

def preB (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match p with
  | .assign _ e => sb e
  | .set _ e => sb e + 12
  | .store e _ => sb e + 24
  | .shareInst _ _ e => sb e + 13
  | p => optP p

def preX (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match p with
  | .assign _ _ | .set _ _ | .store _ _ | .shareInst _ _ _ =>
      (lineBound InitECandidate.Runtime.FineCost.preAllocLeafBudget (WordInst.instSelectExecutable riscvConfig 100000 p)).getD 100000
  | p => optP p

def tag : WordLangProgHOL (BitVec 64) → String
  | .move _ ps => s!"move {ps.length}"
  | .inst _ => "inst" | .assign _ (.const _) => "assignConst" | .assign _ _ => "assign"
  | .get _ _ => "get" | .set _ _ => "set" | .store _ _ => "store" | .tick => "tick"
  | .raise _ => "raise" | .return _ vs => s!"return {vs.length}" | .break _ => "break"
  | .continue _ => "continue" | .opCurrHeap _ _ _ => "opCurrHeap" | .locValue _ _ => "locValue"
  | .shareInst _ _ _ => "shareInst" | .skip => "skip" | _ => "OTHER"

partial def render (price : WordLangProgHOL (BitVec 64) → Nat) (ind : String) : WordLangProgHOL (BitVec 64) → List String
  | .seq a b => render price ind a ++ render price ind b
  | .skip => []
  | .mustTerminate b => render price ind b
  | p@(.ite _ _ _ t e) => [s!"{price p}\t{ind}IF"] ++ render price (ind ++ "  T ") t ++ render price (ind ++ "  E ") e
  | p@(.loop _ b _) => [s!"{price p}\t{ind}LOOP"] ++ render price (ind ++ "  ") b
  | p@(.call rets tgt args _) =>
      let nret := match rets with | some (r, _, _, _, _) => r.length | none => 0
      [s!"{price p}\t{ind}CALL f{tgt} args={args.length} rets={nret}"] ++
        (match rets with | some (_, _, k, _, _) => render price (ind ++ "  K ") k | none => [])
  | p => [s!"{price p}\t{ind}{tag p}"]


open Flapjack.Compiler.Backend.WordSimp

structure W where
  cost : Nat
  dec : List Bool
  used : Nat
  stop : Bool
  cs : Spt (BitVec 64)
  log : List String

/-- walk the executed path, resolving `ite`s constFp resolves (exact constFp constant sets);
others consume recorded decisions (true = T). -/
partial def walkP (price : WordLangProgHOL (BitVec 64) → Nat) (w : W) (p : WordLangProgHOL (BitVec 64)) : W :=
  if w.stop then w else
  match p with
  | .seq a b => walkP price (walkP price w a) b
  | .skip => w
  | .mustTerminate b => walkP price w b
  | .ite cmp lhs rhs t e =>
      let w := { w with cost := w.cost + price p }
      match sptLookup lhs w.cs, getVarImmCs rhs w.cs with
      | some clhs, some crhs =>
          let b := Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp clhs crhs
          walkP price { w with log := s!"static {b}" :: w.log } (if b then t else e)
      | _, _ =>
          let b := w.dec.headD false
          let w' := { w with dec := w.dec.tail, used := w.used + 1, log := s!"dyn {b}" :: w.log }
          walkP price w' (if b then t else e)
  | .loop _ body _ =>
      walkP price { w with cost := w.cost + price p, cs := .ln } body
  | .call ret _ _ handler =>
      let w := { w with cost := w.cost + price p }
      match ret, handler with
      | some (n, names, k, _, _), none =>
          let cs' := deleteAll n (sptFilterV isGcConst (sptInter w.cs (allNames names)))
          walkP price { w with cs := cs' } k
      | some (_, _, k, _, _), some _ => walkP price { w with cs := .ln } k
      | none, _ => { w with stop := true }
  | .return _ _ | .break _ | .continue _ => { w with cost := w.cost + price p, stop := true }
  | q => { w with cost := w.cost + price q, cs := (constFpLoop q w.cs).2 }


/-- Flatten a sequence into its statement list. -/
partial def flat : WordLangProgHOL (BitVec 64) → List (WordLangProgHOL (BitVec 64))
  | .seq a b => flat a ++ flat b
  | .skip => []
  | .mustTerminate b => flat b
  | p => [p]

def isMove : WordLangProgHOL (BitVec 64) → Bool
  | .move _ _ => true
  | _ => false

def isCall : WordLangProgHOL (BitVec 64) → Bool
  | .call _ _ _ _ => true
  | _ => false

structure C where
  cost : Nat := 0
  dec : List Bool
  used : Nat := 0
  stop : Bool := false
  cs : Spt (BitVec 64) := .ln
  /-- (category, move pairs) -/
  cat : List (String × Nat) := []

def C.add (c : C) (k : String) (n : Nat) : C :=
  let rec go : List (String × Nat) → List (String × Nat)
    | [] => [(k, n)]
    | (k', v) :: r => if k' == k then (k', v + n) :: r else (k', v) :: go r
  { c with cat := go c.cat }

/-- Walk a block (statement list) of kind `kind`; moves are classified by position. -/
partial def walkB (kind : String) (seen : Bool) (c : C) : List (WordLangProgHOL (BitVec 64)) → C
  | [] => c
  | p :: rest =>
    if c.stop then c else
    let before := !(c.cat.isEmpty) -- unused
    let _ := before
    match p with
    | .move _ ps =>
      -- leading moves of the block, moves right before a call, trailing moves of the block
      let lead := false
      let _ := lead
      let nextNonMove := rest.find? (fun q => !isMove q)
      let cat :=
        if !seen then kind ++ ":lead"
        else if nextNonMove.isNone then kind ++ ":end"
        else if (nextNonMove.map isCall).getD false then "callPrefix"
        else kind ++ ":body"
      let c := (c.add cat ps.length)
      walkB kind seen { c with cost := c.cost + optP p, cs := (constFpLoop p c.cs).2 } rest
    | .ite cmp lhs rhs t e =>
      let c := { c with cost := c.cost + optP p }
      let (b, c) := match sptLookup lhs c.cs, getVarImmCs rhs c.cs with
        | some clhs, some crhs => (Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp clhs crhs, c)
        | _, _ => (c.dec.headD false, { c with dec := c.dec.tail, used := c.used + 1 })
      let c := walkB "branch" false c (flat (if b then t else e))
      walkB kind true c rest
    | .loop _ body _ =>
      let c := walkB "loop" false { c with cost := c.cost + optP p, cs := .ln } (flat body)
      walkB kind true c rest
    | .call ret _ _ handler =>
      let c := { c with cost := c.cost + optP p }
      match ret, handler with
      | some (n, names, k, _, _), none =>
          let cs' := deleteAll n (sptFilterV isGcConst (sptInter c.cs (allNames names)))
          let c := walkB "ret" false { c with cs := cs' } (flat k)
          walkB kind true c rest
      | some (_, _, k, _, _), some _ =>
          let c := walkB "ret" false { c with cs := .ln } (flat k)
          walkB kind true c rest
      | none, _ => { c with stop := true }
    | .return _ _ | .break _ | .continue _ => { c with cost := c.cost + optP p, stop := true }
    | q => walkB kind true { c with cost := c.cost + optP q, cs := (constFpLoop q c.cs).2 } rest


/-- One executed call site: callee label, args, return names, move pairs right
before it, the call node price, move pairs leading its continuation. -/
structure Site where
  tgt : String
  args : Nat
  rets : Nat
  pre : Nat
  price : Nat
  contLead : Nat

def leadMoves (ps : List (WordLangProgHOL (BitVec 64))) : Nat :=
  ((ps.takeWhile isMove).map (fun q => match q with | .move _ xs => xs.length | _ => 0)).sum

structure D where
  dec : List Bool
  stop : Bool := false
  cs : Spt (BitVec 64) := .ln
  pend : Nat := 0
  sites : List Site := []

partial def walkD (d : D) : List (WordLangProgHOL (BitVec 64)) → D
  | [] => d
  | p :: rest =>
    if d.stop then d else
    match p with
    | .move _ ps => walkD { d with pend := d.pend + ps.length, cs := (constFpLoop p d.cs).2 } rest
    | .ite cmp lhs rhs t e =>
      let (b, d) := match sptLookup lhs d.cs, getVarImmCs rhs d.cs with
        | some clhs, some crhs => (Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp clhs crhs, d)
        | _, _ => (d.dec.headD false, { d with dec := d.dec.tail })
      let d := walkD { d with pend := 0 } (flat (if b then t else e))
      walkD { d with pend := 0 } rest
    | .loop _ body _ =>
      let d := walkD { d with pend := 0, cs := .ln } (flat body)
      walkD { d with pend := 0 } rest
    | .call ret tgt args handler =>
      let nret := match ret with | some (r, _, _, _, _) => r.length | none => 0
      let k := match ret with | some (_, _, k, _, _) => flat k | none => []
      let site : Site := ⟨toString tgt, args.length, nret, d.pend, optP p, leadMoves k⟩
      let d := { d with sites := d.sites ++ [site], pend := 0 }
      match ret, handler with
      | some (n, names, _, _, _), none =>
          let cs' := deleteAll n (sptFilterV isGcConst (sptInter d.cs (allNames names)))
          let d := walkD { d with cs := cs' } k
          walkD { d with pend := 0 } rest
      | some _, some _ =>
          let d := walkD { d with cs := .ln } k
          walkD { d with pend := 0 } rest
      | none, _ => { d with stop := true }
    | .return _ _ | .break _ | .continue _ => { d with stop := true }
    | q => walkD { d with pend := 0, cs := (constFpLoop q d.cs).2 } rest

def decs : List (Nat × String × String) :=
  [(477, "stack_pop", "E"), (478, "stack_push", "EE"), (472, "charge_gas", "E"), (116, "u256_add", ""),
   (492, "pc_add", ""), (499, "op_add", ""), (597, "op_dispatch", "TTET"), (604, "run_frames", "TEEEE")]

#eval do
  for (lab, argc', p) in InitECandidate.Proofs.FrontendStages.Word.outputs do
    match decs.find? (fun (x : Nat × String × String) => x.1 == lab) with
    | some (_, nm, ds0) =>
      let ds := ds0.toList.map (· == 'T')
      let p0 := WordSimp.compileExp p
      let pI := WordInst.instSelectExecutable riscvConfig (maxVarHOL p0 + 1) p0
      let pS := WordAlloc.fullSsaCcTrans argc' pI
      let fin := ((InitECandidate.Proofs.WordBackend.outputs.find? (fun (x : Nat × Nat × WordLangProgHOL (BitVec 64)) => x.1 == lab)).map (fun (x : Nat × Nat × WordLangProgHOL (BitVec 64)) => x.2.2)).getD .skip
      let stages : List (String × WordLangProgHOL (BitVec 64)) := [("isel", pI), ("ssa", pS), ("final", fin)]
      let mut line := s!"FUNC {nm} label {lab} argc {argc'}: entry-lead pairs"
      for ((sn, q) : String × WordLangProgHOL (BitVec 64)) in stages do
        line := line ++ s!" {sn} {leadMoves (flat q)}"
      IO.println line
      let ws := stages.map (fun (x : String × WordLangProgHOL (BitVec 64)) => (x.1, walkD { dec := ds } (flat x.2)))
      let n := ((ws.map (fun (x : String × D) => x.2.sites.length)).foldl max 0)
      for i in List.range n do
        let mut l := s!"  SITE {nm}#{i}"
        for ((sn, d) : String × D) in ws do
          match d.sites[i]? with
          | some st => l := l ++ s!" | {sn}: f{st.tgt} a{st.args} r{st.rets} prefix {st.pre} call {st.price} contLead {st.contLead}"
          | none => l := l ++ s!" | {sn}: -"
        IO.println l
    | none => pure ()
