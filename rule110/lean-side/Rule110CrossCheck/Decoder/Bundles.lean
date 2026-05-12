import Rule110CrossCheck.Decoder.Events

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

def markLabel : BMark -> String
  | BMark.b0 => "b0"
  | BMark.b1 => "b1"

def histLabel : BHist -> String
  | BHist.Empty => "Empty"
  | BHist.e0 h => "e0(" ++ histLabel h ++ ")"
  | BHist.e1 h => "e1(" ++ histLabel h ++ ")"

def natListLabel : List Nat -> String
  | [] => "[]"
  | x :: xs => "[" ++ toString x ++ xs.foldl (fun acc y => acc ++ "," ++ toString y) "" ++ "]"

def parseBundleTerminatedBy (events : List RawEvent) (isEnd : RawEvent -> Bool) :
    Except String (List Nat × List RawEvent) := do
  let rec go (acc : List Nat) : List RawEvent -> Except String (List Nat × List RawEvent)
    | [] => throw "unterminated bundle"
    | event :: rest =>
        if isEnd event then
          pure (acc.reverse, rest)
        else do
          let probe <- parseUnaryNatEvent event
          go (probe :: acc) rest
  go [] events

def parseEmptyTerminatedBundle (events : List RawEvent) : Except String (List Nat × List RawEvent) :=
  parseBundleTerminatedBy events (fun e => rawEventEq e [])

def parseReservedTerminatedBundle (events : List RawEvent) : Except String (List Nat × List RawEvent) :=
  parseBundleTerminatedBy events (fun e => rawEventEq e [BMark.b1, BMark.b1])

def parseBundleFor (family : Family) (events : List RawEvent) : Except String (List Nat × List RawEvent) :=
  match family with
  | .bundleLength | .bundleMembership | .package => parseReservedTerminatedBundle events
  | _ => parseEmptyTerminatedBundle events

def parseNBundlesFor (family : Family) : Nat -> List RawEvent -> Except String (List (List Nat) × List RawEvent)
  | 0, events => pure ([], events)
  | n + 1, events => do
      let (bundle, rest) <- parseBundleFor family events
      let (tail, final) <- parseNBundlesFor family n rest
      pure (bundle :: tail, final)

def parseBHistFromEvents (events : List RawEvent) : Except String (BHist × List RawEvent) :=
  match events with
  | event :: rest => pure (parseBHistEvent event, rest)
  | [] => throw "expected BHist event"

def parseNatFromEvents (events : List RawEvent) : Except String (Nat × List RawEvent) :=
  match events with
  | event :: rest => do
      let n <- parseUnaryNatEvent event
      pure (n, rest)
  | [] => throw "expected unary nat event"

def parseBMarkFromEvents (events : List RawEvent) : Except String (BMark × List RawEvent) :=
  match events with
  | event :: rest => do
      let m <- parseBMarkEvent event
      pure (m, rest)
  | [] => throw "expected mark event"

def parseTwoBitsFromEvents (events : List RawEvent) : Except String ((Bool × Bool) × List RawEvent) :=
  match events with
  | event :: rest => do
      let bits <- parseTwoBitEvent event
      pure (bits, rest)
  | [] => throw "expected two-bit relation event"

def requireNoRest (rest : List RawEvent) : Except String Unit :=
  match rest with
  | [] => pure ()
  | _ => throw s!"trailing input: {rest.length} event(s)"

end BEDC.Rule110CrossCheck
