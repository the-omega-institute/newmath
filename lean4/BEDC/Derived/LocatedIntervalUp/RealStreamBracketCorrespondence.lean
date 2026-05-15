import BEDC.Derived.LocatedIntervalUp

namespace BEDC.Derived.LocatedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedIntervalPacket_real_stream_bracket_correspondence [AskSetup] [PackageSetup]
    {lower upper rationalCells dyadicRefinements streamWindows readbacks seals transport routes
      provenance nameCert endpoint endpointPrime endpointCell realStream bracketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedIntervalPacket lower upper rationalCells dyadicRefinements streamWindows readbacks
        seals transport routes provenance nameCert endpoint bundle pkg ->
      Cont rationalCells dyadicRefinements endpointPrime ->
        Cont endpointPrime streamWindows endpointCell ->
          Cont streamWindows readbacks realStream ->
            Cont endpointCell realStream bracketRead ->
              PkgSig bundle endpointCell pkg ->
                PkgSig bundle realStream pkg ->
                  PkgSig bundle bracketRead pkg ->
                    UnaryHistory endpointPrime ∧ UnaryHistory endpointCell ∧
                      UnaryHistory realStream ∧ UnaryHistory bracketRead ∧
                        hsame endpoint endpointPrime ∧
                          Cont rationalCells dyadicRefinements endpointPrime ∧
                            Cont endpointPrime streamWindows endpointCell ∧
                              Cont streamWindows readbacks realStream ∧
                                Cont endpointCell realStream bracketRead ∧
                                  PkgSig bundle endpointCell pkg ∧
                                    PkgSig bundle realStream pkg ∧
                                      PkgSig bundle bracketRead pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro packet endpointPrimeRoute endpointCellRoute realStreamRoute bracketReadRoute
    endpointCellPkg realStreamPkg bracketReadPkg
  obtain ⟨_lowerUnary, _upperUnary, rationalCellsUnary, dyadicUnary, streamWindowsUnary,
    readbacksUnary, _sealsUnary, _nameCertUnary, _rationalCellsRoute, endpointRoute,
    _transportRoute, _routesRoute, _provenanceRoute, _endpointPkg⟩ := packet
  have endpointPrimeUnary : UnaryHistory endpointPrime :=
    unary_cont_closed rationalCellsUnary dyadicUnary endpointPrimeRoute
  have endpointCellUnary : UnaryHistory endpointCell :=
    unary_cont_closed endpointPrimeUnary streamWindowsUnary endpointCellRoute
  have realStreamUnary : UnaryHistory realStream :=
    unary_cont_closed streamWindowsUnary readbacksUnary realStreamRoute
  have bracketReadUnary : UnaryHistory bracketRead :=
    unary_cont_closed endpointCellUnary realStreamUnary bracketReadRoute
  have sameEndpoint : hsame endpoint endpointPrime :=
    cont_respects_hsame (hsame_refl rationalCells) (hsame_refl dyadicRefinements)
      endpointRoute endpointPrimeRoute
  exact
    ⟨endpointPrimeUnary, endpointCellUnary, realStreamUnary, bracketReadUnary, sameEndpoint,
      endpointPrimeRoute, endpointCellRoute, realStreamRoute, bracketReadRoute, endpointCellPkg,
      realStreamPkg, bracketReadPkg⟩

end BEDC.Derived.LocatedIntervalUp
