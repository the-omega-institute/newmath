import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TailCofinalityScheduleCarrier [AskSetup] [PackageSetup]
    (precision window dyadic regseq sealRow transport route provenance localCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
    UnaryHistory regseq ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        UnaryHistory endpoint ∧ Cont precision window dyadic ∧
          Cont dyadic regseq sealRow ∧ Cont sealRow transport route ∧
            Cont route provenance endpoint ∧ hsame endpoint (append provenance localCert) ∧
              PkgSig bundle endpoint pkg

theorem TailCofinalityScheduleCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
      provenance localCert endpoint bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
            provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro carrier
  have carrierSource := carrier
  obtain ⟨_precisionUnary, _windowUnary, _dyadicUnary, _regseqUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _precisionWindowRoute, _dyadicRegseqRoute, _sealTransportRoute,
    _routeProvenanceRoute, _endpointLocalCert, endpointPkg⟩ := carrier
  have sourceEndpoint :
      (fun row : BHist =>
        TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
          provenance localCert endpoint bundle pkg ∧ hsame row endpoint) endpoint := by
    exact And.intro carrierSource (hsame_refl endpoint)
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source.right
    ledger_sound := by
      intro _row source
      exact And.intro source.right endpointPkg
  }

end BEDC.Derived.TailCofinalityScheduleUp
