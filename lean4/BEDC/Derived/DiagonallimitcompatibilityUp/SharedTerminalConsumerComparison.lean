import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_shared_terminal_consumer_comparison
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      envelope refinement terminalEnvelope terminalRefinement commonEnvelope commonRefinement
      hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory envelope ->
        UnaryHistory refinement ->
          Cont readback realSeal terminalEnvelope ->
            Cont readback realSeal terminalRefinement ->
              Cont terminalEnvelope envelope commonEnvelope ->
                Cont terminalRefinement refinement commonRefinement ->
                  PkgSig bundle commonEnvelope pkg ->
                    PkgSig bundle commonRefinement pkg ->
                      UnaryHistory terminalEnvelope ∧ UnaryHistory terminalRefinement ∧
                        UnaryHistory commonEnvelope ∧ UnaryHistory commonRefinement ∧
                          hsame terminalEnvelope terminalRefinement ∧
                            Cont terminalEnvelope envelope commonEnvelope ∧
                              Cont terminalRefinement refinement commonRefinement ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle commonEnvelope pkg ∧
                                    PkgSig bundle commonRefinement pkg ∧
                                      (Cont commonEnvelope (BHist.e0 hostTail)
                                          terminalRefinement -> False) ∧
                                        (Cont commonEnvelope (BHist.e1 hostTail)
                                            terminalEnvelope -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier envelopeUnary refinementUnary readbackTerminalEnvelope
    readbackTerminalRefinement terminalEnvelopeCommon terminalRefinementCommon commonEnvelopePkg
    commonRefinementPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, _windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have terminalEnvelopeUnary : UnaryHistory terminalEnvelope :=
    unary_cont_closed readbackUnary realSealUnary readbackTerminalEnvelope
  have terminalRefinementUnary : UnaryHistory terminalRefinement :=
    unary_cont_closed readbackUnary realSealUnary readbackTerminalRefinement
  have commonEnvelopeUnary : UnaryHistory commonEnvelope :=
    unary_cont_closed terminalEnvelopeUnary envelopeUnary terminalEnvelopeCommon
  have commonRefinementUnary : UnaryHistory commonRefinement :=
    unary_cont_closed terminalRefinementUnary refinementUnary terminalRefinementCommon
  have terminalSame : hsame terminalEnvelope terminalRefinement :=
    cont_deterministic readbackTerminalEnvelope readbackTerminalRefinement
  exact
    ⟨terminalEnvelopeUnary, terminalRefinementUnary, commonEnvelopeUnary,
      commonRefinementUnary, terminalSame, terminalEnvelopeCommon, terminalRefinementCommon,
      provenancePkg, commonEnvelopePkg, commonRefinementPkg,
      (fun commonBack =>
        let commonBackEnvelope : Cont commonEnvelope (BHist.e0 hostTail) terminalEnvelope :=
          cont_result_hsame_transport commonBack (hsame_symm terminalSame)
        cont_mutual_extension_right_tail_absurd.left terminalEnvelopeCommon
          commonBackEnvelope),
      (fun commonBack =>
        cont_mutual_extension_right_tail_absurd.right terminalEnvelopeCommon commonBack)⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
