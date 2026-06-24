import BEDC.Derived.ObserverperspectiveclassifierUp

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierSiblingCarrierDependency [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route provenance
      name siblingRead verdict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg ->
      Cont observerLeft observerRight siblingRead ->
        Cont siblingRead locality verdict ->
          PkgSig bundle verdict pkg ->
            UnaryHistory observerLeft /\ UnaryHistory observerRight /\
              UnaryHistory universeLeft /\ UnaryHistory universeRight /\ UnaryHistory locality /\
                UnaryHistory siblingRead /\ UnaryHistory verdict /\
                  Cont observerLeft observerRight siblingRead /\
                    Cont siblingRead locality verdict /\
                      PkgSig bundle provenance pkg /\ PkgSig bundle name pkg /\
                        PkgSig bundle verdict pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier observerSibling siblingVerdict verdictPkg
  obtain ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
    localityUnary, _gapUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _observerUniverse, _universeLocality, _localityTransport, _transportGap, provenancePkg,
    namePkg⟩ := carrier
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed observerLeftUnary observerRightUnary observerSibling
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed siblingUnary localityUnary siblingVerdict
  exact
    ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary, localityUnary,
      siblingUnary, verdictUnary, observerSibling, siblingVerdict, provenancePkg, namePkg,
      verdictPkg⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
