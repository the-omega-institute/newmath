import BEDC.Derived.SequentiallyCompleteMetricUp.NameCertObligations

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SequentiallyCompleteMetricFiniteCauchyWindow [AskSetup] [PackageSetup]
    (X S R M L D H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  SequentiallyCompleteMetricCarrier X S M L D H C P N bundle pkg ∧
    UnaryHistory R ∧ Cont S R D ∧ PkgSig bundle P pkg

theorem SequentiallyCompleteMetricFiniteCauchyWindow_admission [AskSetup] [PackageSetup]
    {X S R M L D H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentiallyCompleteMetricCarrier X S M L D H C P N bundle pkg →
      UnaryHistory R →
        Cont S R D →
          PkgSig bundle P pkg →
            SequentiallyCompleteMetricFiniteCauchyWindow X S R M L D H C P N bundle pkg ∧
              UnaryHistory D := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier rUnary finiteWindow provenancePkg
  have carrierProof := carrier
  obtain ⟨_xUnary, sUnary, _mUnary, _lUnary, _dUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _sourceRoute, _limitRoute, _transportName, _carrierPkg⟩ := carrier
  exact
    ⟨⟨carrierProof, rUnary, finiteWindow, provenancePkg⟩,
      unary_cont_closed sUnary rUnary finiteWindow⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
