import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCarrier_tail_modulus_comparison_obligation [AskSetup]
    [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert
      comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
        provenance nameCert bundle pkg →
      Cont tailWindow ledger comparisonRead →
        PkgSig bundle comparisonRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
                  hsame row ledger ∨ hsame row comparisonRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont tailWindow ledger comparisonRead ∧
                  PkgSig bundle comparisonRead pkg ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory comparisonRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier comparisonRoute comparisonPkg
  obtain ⟨tailWindowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailWindowModulus,
    _modulusTolerance, _ledgerSeal, _routesNameCert, provenancePkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed tailWindowUnary ledgerUnary comparisonRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparisonRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
              hsame row ledger ∨ hsame row comparisonRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tailWindow ledger comparisonRead ∧
              PkgSig bundle comparisonRead pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro comparisonRead ⟨hsame_refl comparisonRead, comparisonUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, comparisonRoute, comparisonPkg, provenancePkg⟩
  }
  exact ⟨cert, comparisonUnary⟩

end BEDC.Derived.CauchyOscillationUp
