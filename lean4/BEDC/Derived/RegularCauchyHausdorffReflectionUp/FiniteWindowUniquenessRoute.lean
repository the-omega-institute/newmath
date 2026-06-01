import BEDC.Derived.RegularCauchyHausdorffReflectionUp.RepresentativeIndependence
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.RegularCauchyHausdorffReflectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem RegularCauchyHausdorffReflectionCarrier_finite_window_uniqueness_route
    [AskSetup] [PackageSetup]
    {x : RegularCauchyHausdorffReflectionUp}
    {leftRight dyadicRead uniquenessRead realRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont x.leftWindow x.rightWindow leftRight ->
      Cont leftRight x.toleranceLedger dyadicRead ->
        Cont dyadicRead x.uniquenessRow uniquenessRead ->
          Cont uniquenessRead x.realSeal realRead ->
            Cont realRead x.localNameCert consumer ->
              PkgSig bundle consumer pkg ->
                regularCauchyHausdorffReflectionFromEventFlow
                    (regularCauchyHausdorffReflectionToEventFlow x) =
                  some x ∧
                  Cont leftRight x.toleranceLedger dyadicRead ∧
                    Cont dyadicRead x.uniquenessRow uniquenessRead ∧
                      Cont uniquenessRead x.realSeal realRead ∧
                        Cont realRead x.localNameCert consumer ∧
                          PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg
  intro leftRightRoute dyadicRoute uniquenessRoute realRoute consumerRoute consumerPkg
  have representativeRoute :=
    RegularCauchyHausdorffReflectionRepresentativeIndependence
      leftRightRoute dyadicRoute uniquenessRoute realRoute
  exact
    ⟨representativeRoute.left, dyadicRoute, representativeRoute.right.left,
      representativeRoute.right.right, consumerRoute, consumerPkg⟩

end BEDC.Derived.RegularCauchyHausdorffReflectionUp
