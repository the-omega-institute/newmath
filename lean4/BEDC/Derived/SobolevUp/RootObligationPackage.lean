import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_root_obligation_package [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert rootRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont gradient provenance rootRead ->
        PkgSig bundle rootRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row domain ∨ hsame row magnitude ∨ hsame row gradient ∨
                  hsame row rootRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle rootRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory rootRead ∧ Cont domain base codomain ∧
              Cont codomain magnitude gradient ∧ Cont gradient transports routes ∧
                Cont routes provenance localCert ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier gradientProvenanceRoot rootPkg
  obtain ⟨_domainUnary, _baseUnary, _codomainUnary, _magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, provenanceUnary, _localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed gradientUnary provenanceUnary gradientProvenanceRoot
  have sourceRoot :
      (fun row : BHist => hsame row rootRead ∧ UnaryHistory row) rootRead := by
    exact ⟨hsame_refl rootRead, rootUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row rootRead ∧ UnaryHistory row) hsame := by
    exact {
      carrier_inhabited := Exists.intro rootRead sourceRoot
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _left _middle _right sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameOtherRoot : hsame other rootRead :=
          hsame_trans (hsame_symm same) sourceRow.left
        have otherUnary : UnaryHistory other :=
          unary_transport sourceRow.right same
        exact ⟨sameOtherRoot, otherUnary⟩
    }
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row magnitude ∨ hsame row gradient ∨
              hsame row rootRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle rootRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr sourceRow.left))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, rootPkg, provenancePkg⟩
    }
  exact
    ⟨cert, rootUnary, domainBaseCodomain, codomainMagnitudeGradient,
      gradientTransportsRoutes, routesProvenanceLocalCert, provenancePkg⟩

end BEDC.Derived.SobolevUp
