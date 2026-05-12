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
import Rule110CrossCheck.Parser
import Rule110CrossCheck.Registry

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

deriving instance BEq for BEDC.GroundCompiler.EventFlow.DisplayAlphabet

def markEq (a b : BMark) : Bool :=
  match a, b with
  | BMark.b0, BMark.b0 => true
  | BMark.b1, BMark.b1 => true
  | _, _ => false

def rawEventEq : RawEvent -> RawEvent -> Bool
  | [], [] => true
  | a :: as, b :: bs => markEq a b && rawEventEq as bs
  | _, _ => false

abbrev ProbeNat := Nat
abbrev EvidenceBit := BMark

def histDepth : BHist -> Nat
  | BHist.Empty => 0
  | BHist.e0 h => Nat.succ (histDepth h)
  | BHist.e1 h => Nat.succ (histDepth h)

def appendHist : BHist -> BHist -> BHist :=
  BEDC.FKernel.Cont.append

def extResult (h : BHist) : BMark -> BHist
  | BMark.b0 => BHist.e0 h
  | BMark.b1 => BHist.e1 h

def askExpected (p : Nat) (h : BHist) : BMark :=
  if (p + histDepth h) % 2 = 0 then BMark.b0 else BMark.b1

instance parityAskSetup : AskSetup where
  ProbeName := Nat
  Evidence := BMark
  Ask := fun p h m ev => m = askExpected p h ∧ ev = askExpected p h

instance signaturePackageSetup : PackageSetup :=
  BEDC.FKernel.Package.SignaturePackageSetup

instance boundedDomainSetup : DomainSetup where
  Domain := Nat
  InDom := fun bound h => histDepth h <= bound

end BEDC.Rule110CrossCheck
