import Rule110CrossCheck.Decoder.Fields

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Ext
open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary
open BEDC.FKernel.Package
open BEDC.FKernel.Gap
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.ChannelEncoding
open BEDC.GroundCompiler.EventFlow

namespace BEDC.Rule110CrossCheck

def bitStringToDisplay (bits : String) : Except String (List DisplayAlphabet) := do
  bits.toList.mapM fun
    | '0' => pure BMark.b0
    | '1' => pure BMark.b1
    | c => throw s!"non-binary input character: {c}"

def parseBMarkEvent (w : RawEvent) : Except String BMark :=
  match w with
  | [BMark.b0] => pure BMark.b0
  | [BMark.b1] => pure BMark.b1
  | [] => throw "event is empty, not a BMark payload"
  | _ => throw "event has more than one payload symbol, not a BMark payload"

def parseBitEvent (w : RawEvent) : Except String Bool :=
  match w with
  | [BMark.b0] => pure false
  | [BMark.b1] => pure true
  | _ => throw "event is not a one-bit payload"

def parseTwoBitEvent (w : RawEvent) : Except String (Bool × Bool) :=
  match w with
  | [a, b] => pure (markEq a BMark.b1, markEq b BMark.b1)
  | _ => throw "event is not a two-bit payload"

def parseBHistEvent : RawEvent -> BHist
  | [] => BHist.Empty
  | BMark.b0 :: rest => BHist.e0 (parseBHistEvent rest)
  | BMark.b1 :: rest => BHist.e1 (parseBHistEvent rest)

def parseUnaryNatEvent (w : RawEvent) : Except String Nat :=
  match w.reverse with
  | BMark.b1 :: rest =>
      if rest.all (fun m => markEq m BMark.b0) then pure rest.length
      else throw "unary nat event has nonzero prefix"
  | _ => throw "unary nat event must be nonempty and end with b1"

def decodeEvent (symbols : List DisplayAlphabet) : Except String (RawEvent × List DisplayAlphabet) :=
  match DecEvent symbols with
  | some pair => pure pair
  | none => throw "could not decode event"

partial def decodeAllEventsFuel : Nat -> List DisplayAlphabet -> Except String (List RawEvent)
  | 0, [] => pure []
  | 0, _ :: _ => throw "event stream decoder exhausted fuel"
  | _ + 1, [] => pure []
  | fuel + 1, symbols => do
      let (event, rest) <- decodeEvent symbols
      let tail <- decodeAllEventsFuel fuel rest
      pure (event :: tail)

def decodeAllEvents (bits : String) : Except String (List RawEvent) := do
  let symbols <- bitStringToDisplay bits
  decodeAllEventsFuel symbols.length symbols

def decodeExactlyEvents (bits : String) (n : Nat) : Except String (List RawEvent) := do
  let events <- decodeAllEvents bits
  if events.length = n then pure events
  else throw s!"expected {n} event(s), decoded {events.length}"

def decodeTwoWith (bits : String) (parse : RawEvent -> Except String α) : Except String (α × α) := do
  match (← decodeExactlyEvents bits 2) with
  | [a, b] => pure (← parse a, ← parse b)
  | _ => throw "internal arity mismatch"

def decodeThreeWith (bits : String) (parse : RawEvent -> Except String α) : Except String (α × α × α) := do
  match (← decodeExactlyEvents bits 3) with
  | [a, b, c] => pure (← parse a, ← parse b, ← parse c)
  | _ => throw "internal arity mismatch"

def decodeTwoBMarks (bits : String) : Except String (BMark × BMark) :=
  decodeTwoWith bits parseBMarkEvent

def decodeThreeBMarks (bits : String) : Except String (BMark × BMark × BMark) :=
  decodeThreeWith bits parseBMarkEvent

def decodeTwoBHists (bits : String) : Except String (BHist × BHist) :=
  decodeTwoWith bits (fun e => pure (parseBHistEvent e))

def decodeThreeBHists (bits : String) : Except String (BHist × BHist × BHist) :=
  decodeThreeWith bits (fun e => pure (parseBHistEvent e))

def decodeExtTriple (bits : String) : Except String (BHist × BMark × BHist) := do
  match (← decodeExactlyEvents bits 3) with
  | [source, mark, result] =>
      pure (parseBHistEvent source, ← parseBMarkEvent mark, parseBHistEvent result)
  | _ => throw "internal arity mismatch"

end BEDC.Rule110CrossCheck
