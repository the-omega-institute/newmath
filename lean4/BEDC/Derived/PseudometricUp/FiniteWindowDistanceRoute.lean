import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_finite_window_distance_route [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      distanceRead sealedDistance zeroBoundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg →
      Cont distance stream distanceRead →
        Cont distanceRead sealRow sealedDistance →
          Cont zeroRow transport zeroBoundaryRead →
            PkgSig bundle sealedDistance pkg →
              PkgSig bundle zeroBoundaryRead pkg →
                UnaryHistory point ∧ UnaryHistory distanceRead ∧
                  UnaryHistory sealedDistance ∧ UnaryHistory zeroBoundaryRead ∧
                    Cont distance stream distanceRead ∧ Cont stream readback dyadic ∧
                      Cont dyadic sealRow zeroRow ∧
                        Cont distanceRead sealRow sealedDistance ∧
                          Cont zeroRow transport zeroBoundaryRead ∧
                            PkgSig bundle localName pkg ∧
                              PkgSig bundle sealedDistance pkg ∧
                                PkgSig bundle zeroBoundaryRead pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle PkgSig
  intro carrier distanceRoute sealedRoute zeroBoundaryRoute sealedPkg zeroBoundaryPkg
  obtain ⟨pointUnary, distanceUnary, _dyadicUnary, streamUnary, _readbackUnary, sealUnary,
    zeroUnary, transportUnary, _replayUnary, _localNameUnary, streamReadbackDyadic,
    dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have distanceReadUnary : UnaryHistory distanceRead :=
    unary_cont_closed distanceUnary streamUnary distanceRoute
  have sealedDistanceUnary : UnaryHistory sealedDistance :=
    unary_cont_closed distanceReadUnary sealUnary sealedRoute
  have zeroBoundaryUnary : UnaryHistory zeroBoundaryRead :=
    unary_cont_closed zeroUnary transportUnary zeroBoundaryRoute
  exact
    ⟨pointUnary, distanceReadUnary, sealedDistanceUnary, zeroBoundaryUnary, distanceRoute,
      streamReadbackDyadic, dyadicSealZero, sealedRoute, zeroBoundaryRoute, localNamePkg,
      sealedPkg, zeroBoundaryPkg⟩

end BEDC.Derived.PseudometricUp
