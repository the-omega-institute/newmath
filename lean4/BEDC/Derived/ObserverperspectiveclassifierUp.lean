import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ObserverperspectiveclassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ObserverPerspectiveClassifierCarrier [AskSetup] [PackageSetup]
    (observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧
    UnaryHistory universeLeft ∧ UnaryHistory universeRight ∧ UnaryHistory locality ∧
      UnaryHistory gap ∧ UnaryHistory transport ∧ UnaryHistory route ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont observerLeft observerRight universeLeft ∧
            Cont universeLeft universeRight locality ∧ Cont locality gap transport ∧
              Cont transport route gap ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg

theorem ObserverPerspectiveClassifierNonescape [AskSetup] [PackageSetup]
    {observerLeft observerRight universeLeft universeRight locality gap transport route
      provenance name publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ObserverPerspectiveClassifierCarrier observerLeft observerRight universeLeft universeRight
        locality gap transport route provenance name bundle pkg →
      Cont observerLeft publicRead gap →
        PkgSig bundle publicRead pkg →
          UnaryHistory observerLeft ∧ UnaryHistory observerRight ∧
            UnaryHistory universeLeft ∧ UnaryHistory universeRight ∧ UnaryHistory locality ∧
              UnaryHistory gap ∧ UnaryHistory publicRead ∧ Cont observerLeft publicRead gap ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier observerPublicGap publicReadPkg
  obtain ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
    localityUnary, gapUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    _observerUniverse, _universeLocality, _localityTransport, _transportGap, provenancePkg,
    namePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_right_factor observerPublicGap gapUnary
  exact
    ⟨observerLeftUnary, observerRightUnary, universeLeftUnary, universeRightUnary,
      localityUnary, gapUnary, publicReadUnary, observerPublicGap, provenancePkg, namePkg,
      publicReadPkg⟩

end BEDC.Derived.ObserverperspectiveclassifierUp
