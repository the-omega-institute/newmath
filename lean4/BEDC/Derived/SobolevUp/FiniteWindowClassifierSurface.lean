import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevFiniteWindowClassifierSurface [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient trace transports provenance localCert
      classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevFiniteWindowCarrier domain base codomain magnitude gradient trace transports
        provenance localCert bundle pkg ->
      Cont domain gradient classifierRead ->
        PkgSig bundle classifierRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
                  hsame row magnitude ∨ hsame row gradient ∨ hsame row trace ∨
                    hsame row classifierRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle classifierRead pkg)
              hsame ∧
            UnaryHistory classifierRead ∧ Cont domain base codomain ∧
              Cont codomain magnitude gradient ∧ Cont gradient trace transports := by
  -- BEDC touchpoint anchor: SobolevFiniteWindowCarrier BHist Cont ProbeBundle PkgSig
  intro carrier domainGradientClassifier classifierPkg
  obtain ⟨domainUnary, _baseUnary, _codomainUnary, _magnitudeUnary, gradientUnary,
    _traceUnary, _transportsUnary, _provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTraceTransports, provenancePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed domainUnary gradientUnary domainGradientClassifier
  have sourceClassifier :
      (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
        classifierRead := by
    exact ⟨hsame_refl classifierRead, classifierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
              hsame row magnitude ∨ hsame row gradient ∨ hsame row trace ∨
                hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead sourceClassifier
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
      exact ⟨source.right, provenancePkg, classifierPkg⟩
  }
  exact
    ⟨cert, classifierUnary, domainBaseCodomain, codomainMagnitudeGradient,
      gradientTraceTransports⟩

end BEDC.Derived.SobolevUp
