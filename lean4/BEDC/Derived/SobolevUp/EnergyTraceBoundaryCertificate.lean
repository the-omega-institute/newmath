import BEDC.Derived.SobolevUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_energy_trace_boundary_certificate [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert energyRead
      traceRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance localCert
        bundle pkg →
      Cont magnitude gradient energyRead →
        Cont energyRead localCert traceRead →
          Cont traceRead provenance boundaryRead →
            PkgSig bundle boundaryRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
                      hsame row magnitude ∨ hsame row gradient ∨ hsame row energyRead ∨
                        hsame row traceRead ∨ hsame row boundaryRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont domain base codomain ∧
                      Cont codomain magnitude gradient ∧ Cont magnitude gradient energyRead ∧
                        Cont energyRead localCert traceRead ∧
                          Cont traceRead provenance boundaryRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg)
                  hsame ∧
                UnaryHistory energyRead ∧ UnaryHistory traceRead ∧
                  UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier magnitudeGradientEnergy energyLocalTrace traceProvenanceBoundary boundaryPkg
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, provenanceUnary, localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed magnitudeUnary gradientUnary magnitudeGradientEnergy
  have traceUnary : UnaryHistory traceRead :=
    unary_cont_closed energyUnary localCertUnary energyLocalTrace
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed traceUnary provenanceUnary traceProvenanceBoundary
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row base ∨ hsame row codomain ∨ hsame row magnitude ∨
              hsame row gradient ∨ hsame row energyRead ∨ hsame row traceRead ∨
                hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
              Cont magnitude gradient energyRead ∧ Cont energyRead localCert traceRead ∧
                Cont traceRead provenance boundaryRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead
        ⟨hsame_refl boundaryRead, boundaryUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, domainBaseCodomain, codomainMagnitudeGradient,
          magnitudeGradientEnergy, energyLocalTrace, traceProvenanceBoundary, provenancePkg,
          boundaryPkg⟩
  }
  exact ⟨cert, energyUnary, traceUnary, boundaryUnary⟩

end BEDC.Derived.SobolevUp
