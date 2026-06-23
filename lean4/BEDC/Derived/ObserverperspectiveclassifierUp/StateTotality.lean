import BEDC.Derived.ObserverperspectiveclassifierUp

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierStateTotality [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name verdict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont locality gap verdict →
        PkgSig bundle verdict pkg →
          UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧
            UnaryHistory universeLeft ∧ UnaryHistory universeRight ∧ UnaryHistory locality ∧
              UnaryHistory gap ∧ UnaryHistory verdict ∧
                Cont observerLeft observerRight universeLeft ∧
                  Cont universeLeft universeRight locality ∧ Cont locality gap verdict ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle verdict pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier localityGapVerdict verdictPkg
  obtain
    ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
      localityUnary, gapUnary, _transportUnary, _routeUnary, _provenanceUnary,
      _nameUnary, observerUniverse, universeLocality, _localityTransport, _transportGap,
      provenancePkg, namePkg⟩ := carrier
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed localityUnary gapUnary localityGapVerdict
  exact
    ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
      localityUnary, gapUnary, verdictUnary, observerUniverse, universeLocality,
      localityGapVerdict, provenancePkg, namePkg, verdictPkg⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
