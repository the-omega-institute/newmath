import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont

/-! Placeholder unary-history example scaffolding for later concrete developments. -/
namespace BEDC.FKernel.Examples.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Gap
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

local instance : AskSetup := MinimalAskSetup
local instance : PackageSetup := MinimalPackageSetup
local instance : DomainSetup := MinimalDomainSetup
local instance : NameCertSetup := MinimalNameCertSetup

def UnaryHistory : BHist → Prop
  | .Empty => True
  | .e1 h => UnaryHistory h
  | .e0 _ => False

def UnaryBundle : ProbeBundle ProbeName := .Bcons () .Bnil
def UnaryDomain : Domain := ()
def UnaryName : DerivedName := ()

-- Placeholder: source did not give a concrete shape. v0.2 will specify.
theorem unary_addition_seed : True := True.intro

end BEDC.FKernel.Examples.Unary
