import BEDC.FKernel.Mark
import BEDC.FKernel.Hist
import BEDC.FKernel.Ext
import BEDC.FKernel.Cont
import BEDC.FKernel.Bundle
import BEDC.FKernel.Ask
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary
import BEDC.FKernel.ExternalBinary
import BEDC.FKernel.Package
import BEDC.FKernel.Gap
import BEDC.FKernel.NameCert
import BEDC.FKernel.Settled
import BEDC.GroundCompiler.ChannelEncoding
import Rule110CrossCheck.Decoder
import Rule110CrossCheck.Reporting
import Rule110CrossCheck.Families.Gap

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

def checkSettledHistory (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  match subcase with
  | 0 =>
      let (h, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (histDepth h == 1)
  | 1 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (histDepth h == 1 && histDepth k == 1 && h != k)
  | 2 =>
      let (_h, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure true
  | 3 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (k == BHist.e0 h)
  | 4 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (histDepth h <= 1 && histDepth k <= 1)
  | _ => pure false

def checkSettledExtCont (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  match subcase with
  | 0 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (mHist, rest) <- parseBHistFromEvents rest
      let (c, rest) <- parseBHistFromEvents rest
      let (d, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      match mHist with
      | BHist.e0 BHist.Empty => pure (extResult a BMark.b0 == c && extResult a BMark.b0 == d && c == d)
      | BHist.e1 BHist.Empty => pure (extResult a BMark.b1 == c && extResult a BMark.b1 == d && c == d)
      | _ => pure false
  | 1 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      let (c, rest) <- parseBHistFromEvents rest
      let (d, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (appendHist a b == c && appendHist a b == d && c == d)
  | 2 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (appendHist BHist.Empty a == b && a == b)
  | 3 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (appendHist a BHist.Empty == b && a == b)
  | 4 =>
      let (a, rest) <- parseBHistFromEvents rest
      let (b, rest) <- parseBHistFromEvents rest
      let (c, rest) <- parseBHistFromEvents rest
      let (d, rest) <- parseBHistFromEvents rest
      let (e, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      let ab := appendHist a b
      let bc := appendHist b c
      pure (appendHist ab c == d && appendHist a bc == e && d == e)
  | _ => pure false

def checkSettledSignature (subcase : Nat) (rest : List RawEvent) : Except String Bool := do
  let (bundle, rest) <- parseBundleFor .settled rest
  match subcase with
  | 0 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (s, rest) <- parseBHistFromEvents rest
      let (t, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      let computed := sigResult bundle h
      pure (!((computed == s) && (computed == t)) || s == t)
  | 1 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      pure (!sameSigFixture bundle h k || sameSigFixture bundle k h)
  | 2 =>
      let (h, rest) <- parseBHistFromEvents rest
      let (k, rest) <- parseBHistFromEvents rest
      let (l, rest) <- parseBHistFromEvents rest
      requireNoRest rest
      let hk := sameSigFixture bundle h k
      let kl := sameSigFixture bundle k l
      let hl := sameSigFixture bundle h l
      pure (!(hk && kl) || hl)
  | _ => pure false

end BEDC.Rule110CrossCheck
