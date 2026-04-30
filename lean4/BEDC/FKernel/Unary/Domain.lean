import BEDC.FKernel.Unary.History
import BEDC.FKernel.NameCert

namespace BEDC.FKernel.Unary

open BEDC.FKernel.Hist
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Gap
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Cont

local instance : AskSetup := MinimalAskSetup
local instance : PackageSetup := MinimalPackageSetup
local instance : NameCertSetup := MinimalNameCertSetup

def UnaryDomainSetup : DomainSetup where
  Domain := Unit
  InDom := fun _ h => UnaryHistory h

def UnarySourceSpec (h : BHist) : Prop := UnaryHistory h

theorem UnarySourceSpec_iff_unaryHistory {h : BHist} : UnarySourceSpec h ↔ UnaryHistory h := by
  rfl

theorem UnarySourceSpec_induction {P : BHist -> Prop} :
    P BHist.Empty ->
      (forall h : BHist, UnarySourceSpec h -> P h -> P (BHist.e1 h)) ->
      forall h : BHist, UnarySourceSpec h -> P h := by
  intro base step h uh
  exact unary_history_induction base (by intro h uh ph; exact step h uh ph) h uh

local instance : DomainSetup := UnaryDomainSetup

theorem unary_domain_policy :
    @DomainPolicy (G := UnaryDomainSetup) (D := ()) where
  transport := by
    intro h k hh hsamehk
    cases hsamehk
    exact hh

def UnaryBundle : ProbeBundle ProbeName := .Bcons () .Bnil
def UnaryDomain : Domain := ()
def UnaryName : DerivedName := ()
def AddName : DerivedName := ()

theorem unaryDomain_inDom_iff_unaryHistory {h : BHist} :
    InDom UnaryDomain h <-> UnaryHistory h := by
  rfl

theorem unary_domain_gap_transport {bundle : ProbeBundle ProbeName} {p : Pkg} {h k s : BHist} :
    InGapSig bundle UnaryDomain p h -> hsame h k -> BEDC.FKernel.Sig.SigRel bundle k s ->
      TokIntro bundle s p -> InGapSig bundle UnaryDomain p k := by
  intro hgap hhk hsig htok
  exact inGapSig_domain_transport_with_signature
    (bundle := bundle) (D := UnaryDomain) (p := p) (h := h) (k := k) (s := s)
    unary_domain_policy hgap hhk hsig htok

end BEDC.FKernel.Unary
