import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_classifier_locality [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert
      classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg →
      Cont transports routes classifierRead →
        PkgSig bundle classifierRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
                  hsame row magnitude ∨ hsame row gradient ∨ hsame row transports ∨
                    hsame row routes ∨ hsame row provenance ∨ hsame row localCert ∨
                      hsame row classifierRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle classifierRead pkg)
              hsame ∧
            UnaryHistory classifierRead ∧ Cont domain base codomain ∧
              Cont codomain magnitude gradient ∧ Cont gradient transports routes ∧
                Cont transports routes classifierRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier classifierRoute classifierPkg
  obtain ⟨_domainUnary, _baseUnary, _codomainUnary, _magnitudeUnary, _gradientUnary,
    transportsUnary, routesUnary, _provenanceUnary, _localCertUnary, domainRoute,
    magnitudeRoute, transportRoute, _provenanceRoute, provenancePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed transportsUnary routesUnary classifierRoute
  have sourceClassifier :
      (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row) classifierRead :=
    ⟨hsame_refl classifierRead, classifierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row classifierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row base ∨ hsame row codomain ∨
              hsame row magnitude ∨ hsame row gradient ∨ hsame row transports ∨
                hsame row routes ∨ hsame row provenance ∨ hsame row localCert ∨
                  hsame row classifierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle classifierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro classifierRead sourceClassifier
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
        intro _row _row' sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, provenancePkg, classifierPkg⟩
  }
  exact ⟨cert, classifierUnary, domainRoute, magnitudeRoute, transportRoute, classifierRoute⟩

end BEDC.Derived.SobolevUp
