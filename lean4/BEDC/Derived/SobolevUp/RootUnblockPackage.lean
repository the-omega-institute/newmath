import BEDC.Derived.SobolevUp

namespace BEDC.Derived.SobolevUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SobolevCarrier_root_unblock_package [AskSetup] [PackageSetup]
    {domain base codomain magnitude gradient transports routes provenance localCert rootRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevCarrier domain base codomain magnitude gradient transports routes provenance
        localCert bundle pkg ->
      Cont gradient provenance rootRead ->
        Cont rootRead localCert sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row domain ∨ hsame row magnitude ∨ hsame row gradient ∨
                    hsame row rootRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory rootRead ∧ UnaryHistory sealRead ∧ Cont domain base codomain ∧
                Cont codomain magnitude gradient ∧ Cont gradient transports routes ∧
                  Cont routes provenance localCert ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: SobolevCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier gradientProvenanceRoot rootLocalCertSeal sealPkg
  obtain ⟨_domainUnary, _baseUnary, _codomainUnary, _magnitudeUnary, gradientUnary,
    _transportsUnary, _routesUnary, provenanceUnary, localCertUnary, domainBaseCodomain,
    codomainMagnitudeGradient, gradientTransportsRoutes, routesProvenanceLocalCert,
    provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed gradientUnary provenanceUnary gradientProvenanceRoot
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rootUnary localCertUnary rootLocalCertSeal
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row domain ∨ hsame row magnitude ∨ hsame row gradient ∨
              hsame row rootRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, provenancePkg, sealPkg⟩
  }
  exact
    ⟨cert, rootUnary, sealUnary, domainBaseCodomain, codomainMagnitudeGradient,
      gradientTransportsRoutes, routesProvenanceLocalCert, provenancePkg, sealPkg⟩

end BEDC.Derived.SobolevUp
