import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCarrier_dyadic_bound_classifier_obligation [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert dyadicRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg ->
      Cont modulus tolerance dyadicRead ->
        Cont dyadicRead sealRow sealRead ->
          PkgSig bundle provenance pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row dyadicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row modulus ∨ hsame row tolerance ∨ hsame row dyadicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont modulus tolerance dyadicRead ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory dyadicRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier dyadicRoute sealRoute provenancePkg
  obtain ⟨_tailWindowUnary, modulusUnary, toleranceUnary, _ledgerUnary, sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailWindowModulus,
    _modulusTolerance, _ledgerSeal, _routesNameCert, _carrierPkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed modulusUnary toleranceUnary dyadicRoute
  have sealUnaryRead : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary sealUnary sealRoute
  have sourceDyadic :
      (fun row : BHist => hsame row dyadicRead ∧ UnaryHistory row) dyadicRead := by
    exact ⟨hsame_refl dyadicRead, dyadicUnary⟩
  have core :
      NameCert (fun row : BHist => hsame row dyadicRead ∧ UnaryHistory row) hsame := by
    exact {
      carrier_inhabited := Exists.intro dyadicRead sourceDyadic
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
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dyadicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row modulus ∨ hsame row tolerance ∨ hsame row dyadicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus tolerance dyadicRead ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := core
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr source.left)
      ledger_sound := by
        intro _row source
        exact ⟨source.right, dyadicRoute, provenancePkg⟩
    }
  exact ⟨cert, dyadicUnary, sealUnaryRead⟩

end BEDC.Derived.CauchyOscillationUp
