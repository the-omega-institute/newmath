import BEDC.Derived.BoundedRealSequenceUp.NameCertObligations

namespace BEDC.Derived.BoundedRealSequenceUp.FiniteWindowNet

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BoundedRealSequenceFiniteWindowNet [AskSetup] [PackageSetup]
    (S W Q R I H C P N netRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  NameCertObligations.BoundedRealSequenceCarrier S W Q R I H C P N bundle pkg ∧
    Cont S W Q ∧ Cont Q R netRead ∧ PkgSig bundle netRead pkg

theorem BoundedRealSequenceFiniteWindowNet_extraction [AskSetup] [PackageSetup]
    {S W Q R I H C P N netRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedRealSequenceFiniteWindowNet S W Q R I H C P N netRead bundle pkg →
      UnaryHistory Q ∧ UnaryHistory netRead ∧ Cont S W Q ∧ Cont Q R netRead ∧
        PkgSig bundle netRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro net
  obtain ⟨carrier, sourceWindow, readbackRoute, netPkg⟩ := net
  obtain ⟨sourceUnary, windowUnary, _readbackUnary, realUnary, _intervalUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localCertUnary, _intervalRoute,
    _transportSame, _provenancePkg, _localCertPkg⟩ := carrier
  have qUnary : UnaryHistory Q :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed qUnary realUnary readbackRoute
  exact ⟨qUnary, netUnary, sourceWindow, readbackRoute, netPkg⟩

end BEDC.Derived.BoundedRealSequenceUp.FiniteWindowNet
