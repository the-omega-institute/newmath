import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteLebesgueNumberPhaseRealRadiusWindowCarrier [AskSetup] [PackageSetup]
    (request radius dyadicRead window sealRow transport replay provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory request ∧ UnaryHistory radius ∧ UnaryHistory dyadicRead ∧
    UnaryHistory window ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory nameRow ∧
        Cont request radius dyadicRead ∧ Cont dyadicRead window sealRow ∧
          Cont sealRow transport replay ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle nameRow pkg

theorem FiniteLebesgueNumberPhaseRealRadiusWindowCarrier_admission [AskSetup]
    [PackageSetup]
    {request radius dyadicRead window sealRow transport replay provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberPhaseRealRadiusWindowCarrier request radius dyadicRead window sealRow
        transport replay provenance nameRow bundle pkg →
      UnaryHistory dyadicRead ∧ UnaryHistory window ∧ UnaryHistory sealRow ∧
        Cont request radius dyadicRead ∧ Cont dyadicRead window sealRow ∧
          Cont sealRow transport replay ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier
  obtain ⟨_requestUnary, _radiusUnary, dyadicUnary, windowUnary, sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameRowUnary, requestRadiusDyadic,
    dyadicWindowSeal, sealTransportReplay, provenancePkg, nameRowPkg⟩ := carrier
  exact
    ⟨dyadicUnary, windowUnary, sealUnary, requestRadiusDyadic, dyadicWindowSeal,
      sealTransportReplay, provenancePkg, nameRowPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
