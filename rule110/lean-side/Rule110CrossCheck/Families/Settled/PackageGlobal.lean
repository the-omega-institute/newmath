import Rule110CrossCheck.Families.Settled.Basic
import BEDC.GroundCompiler.ChannelEncoding

open BEDC.GroundCompiler.EventFlow

namespace BEDC.Rule110CrossCheck

def checkSettledPackageGap (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  match subcase with
  | 0 => checkGap pathPlaceholder { name := "settled-ingap", input := "", fields := [] } *> pure false
  | 1 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      let (c, rest) <- parseBHistFromEvents rest
      let (d, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (!(a == b && a == c && b == d) || c == d)
  | 2 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (a == b)
  | _ => pure false
where
  pathPlaceholder := ""

def parseInGapTail (rest : List RawEvent) : Except String Bool := do
  let (bound, rest) <- parseNatFromEvents rest
  let (bundle, rest) <- parseBundleFor .gap rest
  let (h, rest) <- parseBHistFromEvents rest
  let (s, rest) <- parseBHistFromEvents rest
  let (p, rest) <- parseBHistFromEvents rest
  requireNoRest rest
  pure (histDepth h <= bound && sigResult bundle h == s && s == p)

def checkSettledGlobalize (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  match subcase with
  | 0 =>
      let (bound, rest) <- parseNatFromEvents rest
      let (bundle, rest) <- parseBundleFor .settled rest
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      let (p, rest) <- parseBHistFromEvents rest
      let (q, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      let sigH := sigResult bundle h
      let sigK := sigResult bundle k
      pure (histDepth h <= bound && histDepth k <= bound && sigH == p && sigK == q && ((p == q) == (sigH == sigK)))
  | 1 =>
      let (bound, rest) <- parseNatFromEvents rest
      let (bundle, rest) <- parseBundleFor .settled rest
      let (h, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (histDepth h <= bound && sigResult bundle h == sigResult bundle h)
  | _ => pure false

end BEDC.Rule110CrossCheck
