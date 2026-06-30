import BEDC.Derived.SobolevUp.FiniteWindowCarrierFields
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_finite_derivative_window_bridge [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient trace transports provenance localCert
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevFiniteWindowCarrier domain base codomain magnitude gradient trace transports
        provenance localCert bundle pkg →
      Cont transports provenance bridgeRead →
        PkgSig bundle bridgeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row domain ∨ hsame row magnitude ∨ hsame row gradient ∨
                  hsame row trace ∨ hsame row transports ∨ hsame row provenance ∨
                    hsame row bridgeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont gradient trace transports ∧
                  Cont transports provenance bridgeRead ∧ PkgSig bundle bridgeRead pkg)
              hsame ∧
            UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: SobolevFiniteWindowCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier transportsProvenanceBridge bridgePkg
  obtain ⟨_domainUnary, _baseUnary, _codomainUnary, _magnitudeUnary, _gradientUnary,
    _traceUnary, transportsUnary, provenanceUnary, _localCertUnary, _domainBaseCodomain,
    _codomainMagnitudeGradient, gradientTraceTransports, _provenancePkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed transportsUnary provenanceUnary transportsProvenanceBridge
  have sourceBridge :
      (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row) bridgeRead := by
    exact ⟨hsame_refl bridgeRead, bridgeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row magnitude ∨ hsame row gradient ∨
              hsame row trace ∨ hsame row transports ∨ hsame row provenance ∨
                hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont gradient trace transports ∧
              Cont transports provenance bridgeRead ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceBridge
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, gradientTraceTransports, transportsProvenanceBridge, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.SobolevUp
