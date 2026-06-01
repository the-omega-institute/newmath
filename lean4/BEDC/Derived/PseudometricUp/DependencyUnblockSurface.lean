import BEDC.Derived.PseudometricUp

namespace BEDC.Derived.PseudometricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PseudometricCarrier_dependency_unblock_surface [AskSetup] [PackageSetup]
    {point distance dyadic stream readback sealRow zeroRow transport replay localName
      distanceRead sealedDistance zeroBoundaryRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PseudometricCarrier point distance dyadic stream readback sealRow zeroRow transport replay
        localName bundle pkg ->
      Cont distance stream distanceRead ->
        Cont distanceRead sealRow sealedDistance ->
          Cont zeroRow transport zeroBoundaryRead ->
            Cont sealedDistance replay completionRead ->
              PkgSig bundle sealedDistance pkg ->
                PkgSig bundle zeroBoundaryRead pkg ->
                  PkgSig bundle completionRead pkg ->
                    UnaryHistory point ∧ UnaryHistory distance ∧ UnaryHistory zeroRow ∧
                      UnaryHistory zeroBoundaryRead ∧ UnaryHistory completionRead ∧
                        Cont distance stream distanceRead ∧
                          Cont zeroRow transport zeroBoundaryRead ∧
                            PkgSig bundle localName pkg ∧
                              PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: PseudometricCarrier BHist Cont ProbeBundle PkgSig
  intro carrier distanceRoute sealedRoute zeroBoundaryRoute completionRoute _sealedPkg
    _zeroBoundaryPkg completionPkg
  obtain ⟨pointUnary, distanceUnary, _dyadicUnary, streamUnary, _readbackUnary,
    _sealUnary, zeroUnary, transportUnary, replayUnary, _localNameUnary,
    _streamReadbackDyadic, _dyadicSealZero, _localNameZero, localNamePkg⟩ := carrier
  have distanceReadUnary : UnaryHistory distanceRead :=
    unary_cont_closed distanceUnary streamUnary distanceRoute
  have sealedDistanceUnary : UnaryHistory sealedDistance :=
    unary_cont_closed distanceReadUnary _sealUnary sealedRoute
  have zeroBoundaryUnary : UnaryHistory zeroBoundaryRead :=
    unary_cont_closed zeroUnary transportUnary zeroBoundaryRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed sealedDistanceUnary replayUnary completionRoute
  exact
    ⟨pointUnary, distanceUnary, zeroUnary, zeroBoundaryUnary, completionUnary,
      distanceRoute, zeroBoundaryRoute, localNamePkg, completionPkg⟩

end BEDC.Derived.PseudometricUp
