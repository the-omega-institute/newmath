import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegulatedRealFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegulatedRealFunctionCarrier [AskSetup] [PackageSetup]
    (interval approxLedger tailLedger uniformRoute endpointSeal transportRow replayRow
      provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory interval ∧ UnaryHistory approxLedger ∧ UnaryHistory tailLedger ∧
    UnaryHistory uniformRoute ∧ UnaryHistory endpointSeal ∧ UnaryHistory transportRow ∧
      UnaryHistory replayRow ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        Cont interval approxLedger tailLedger ∧ Cont tailLedger uniformRoute endpointSeal ∧
          Cont endpointSeal transportRow replayRow ∧ Cont replayRow provenance localCert ∧
            PkgSig bundle provenance pkg

theorem RegulatedRealFunctionCarrier_integration_facing_handoff_boundary [AskSetup]
    [PackageSetup]
    {interval approxLedger tailLedger uniformRoute endpointSeal transportRow replayRow
      provenance localCert integrationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatedRealFunctionCarrier interval approxLedger tailLedger uniformRoute endpointSeal
        transportRow replayRow provenance localCert bundle pkg ->
      Cont endpointSeal replayRow integrationRead ->
        PkgSig bundle integrationRead pkg ->
          UnaryHistory interval ∧ UnaryHistory approxLedger ∧ UnaryHistory tailLedger ∧
            UnaryHistory uniformRoute ∧ UnaryHistory endpointSeal ∧
              UnaryHistory integrationRead ∧ Cont interval approxLedger tailLedger ∧
                Cont tailLedger uniformRoute endpointSeal ∧
                  Cont endpointSeal replayRow integrationRead ∧
                    PkgSig bundle provenance pkg ∧
                      PkgSig bundle integrationRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier endpointReplayRead integrationPkg
  obtain ⟨intervalUnary, approxUnary, tailUnary, uniformUnary, endpointUnary,
    _transportUnary, replayUnary, _provenanceUnary, _localCertUnary, intervalApproxTail,
    tailUniformEndpoint, _endpointTransportReplay, _replayProvenanceLocal,
    provenancePkg⟩ := carrier
  have integrationUnary : UnaryHistory integrationRead :=
    unary_cont_closed endpointUnary replayUnary endpointReplayRead
  exact
    ⟨intervalUnary, approxUnary, tailUnary, uniformUnary, endpointUnary, integrationUnary,
      intervalApproxTail, tailUniformEndpoint, endpointReplayRead, provenancePkg, integrationPkg⟩

theorem RegulatedRealFunctionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {interval approxLedger tailLedger uniformRoute endpointSeal transportRow replayRow
      provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegulatedRealFunctionCarrier interval approxLedger tailLedger uniformRoute endpointSeal
        transportRow replayRow provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegulatedRealFunctionCarrier interval approxLedger tailLedger uniformRoute endpointSeal
            transportRow replayRow provenance localCert bundle pkg ∧ hsame row localCert)
        (fun row : BHist =>
          RegulatedRealFunctionCarrier interval approxLedger tailLedger uniformRoute endpointSeal
            transportRow replayRow provenance localCert bundle pkg ∧ hsame row localCert)
        (fun row : BHist =>
          RegulatedRealFunctionCarrier interval approxLedger tailLedger uniformRoute endpointSeal
            transportRow replayRow provenance localCert bundle pkg ∧ hsame row localCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro localCert (And.intro carrier (hsame_refl localCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.RegulatedRealFunctionUp
