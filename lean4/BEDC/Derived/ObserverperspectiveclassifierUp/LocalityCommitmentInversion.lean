import BEDC.Derived.ObserverperspectiveclassifierUp

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierLocalityCommitmentInversion [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route provenance
      name comparison verdictRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont locality gap comparison →
        Cont gap route verdictRead →
          PkgSig bundle verdictRead pkg →
            UnaryHistory locality ∧ UnaryHistory gap ∧ UnaryHistory comparison ∧
              UnaryHistory verdictRead ∧ hsame comparison transport ∧
                Cont locality gap comparison ∧ Cont gap route verdictRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle verdictRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont PkgSig UnaryHistory
  intro carrier localityGapComparison gapRouteVerdict verdictPkg
  obtain ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary,
    _universeRightUnary, localityUnary, gapUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _observerUniverse, _universeLocality,
    localityTransport, _transportGap, provenancePkg, namePkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed localityUnary gapUnary localityGapComparison
  have verdictUnary : UnaryHistory verdictRead :=
    unary_cont_closed gapUnary routeUnary gapRouteVerdict
  have comparisonSameTransport : hsame comparison transport :=
    cont_deterministic localityGapComparison localityTransport
  exact
    ⟨localityUnary, gapUnary, comparisonUnary, verdictUnary, comparisonSameTransport,
      localityGapComparison, gapRouteVerdict, provenancePkg, namePkg, verdictPkg⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
