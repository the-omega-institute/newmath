import BEDC.Derived.ObserverperspectiveclassifierUp

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ObserverPerspectiveClassifierClassifierDeterminacy [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name verdict verdict' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg ->
      Cont gap route verdict ->
        Cont gap route verdict' ->
          PkgSig bundle verdict pkg ->
            PkgSig bundle verdict' pkg ->
              UnaryHistory verdict ∧ UnaryHistory verdict' ∧ hsame verdict verdict' ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle verdict pkg ∧ PkgSig bundle verdict' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier verdictRead verdictRead' verdictPkg verdictPkg'
  obtain ⟨_observerLeftUnary, _observerRightUnary, _universeLeftUnary,
    _universeRightUnary, _localityUnary, gapUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameUnary, _observerUniverse, _universeLocality, _localityTransport,
    _transportGap, provenancePkg, namePkg⟩ := carrier
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed gapUnary routeUnary verdictRead
  have verdictUnary' : UnaryHistory verdict' :=
    unary_cont_closed gapUnary routeUnary verdictRead'
  have verdictSame : hsame verdict verdict' :=
    cont_deterministic verdictRead verdictRead'
  exact
    ⟨verdictUnary, verdictUnary', verdictSame, provenancePkg, namePkg, verdictPkg,
      verdictPkg'⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
