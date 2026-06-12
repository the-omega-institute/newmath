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

theorem SobolevTraceBoundaryObligationRoute [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert traceRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont gradient localCert traceRead ->
        Cont traceRead provenance boundaryRead ->
          PkgSig bundle boundaryRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
                    hsame row magnitude ∨ hsame row gradient ∨ hsame row traceRead ∨
                      hsame row boundaryRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont domain base codomain ∧
                    Cont codomain magnitude gradient ∧ Cont gradient localCert traceRead ∧
                      Cont traceRead provenance boundaryRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle boundaryRead pkg)
                hsame ∧
              UnaryHistory traceRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier gradientLocalTrace traceProvenanceBoundary boundaryPkg
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, _magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, provenanceUnary, localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, _gradientTransportsRoutes, _routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have traceUnary : UnaryHistory traceRead :=
    unary_cont_closed gradientUnary localCertUnary gradientLocalTrace
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed traceUnary provenanceUnary traceProvenanceBoundary
  have sourceBoundary :
      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, boundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
              hsame row magnitude ∨ hsame row gradient ∨ hsame row traceRead ∨
                hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont domain base codomain ∧ Cont codomain magnitude gradient ∧
              Cont gradient localCert traceRead ∧ Cont traceRead provenance boundaryRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceBoundary
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, domainBaseCodomain, codomainMagnitudeGradient, gradientLocalTrace,
          traceProvenanceBoundary, provenancePkg, boundaryPkg⟩
  }
  exact ⟨cert, traceUnary, boundaryUnary⟩

end BEDC.Derived.SobolevUp
