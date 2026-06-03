import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCarrier_tail_window_cofinality [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert
      tailRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes
        provenance nameCert bundle pkg ->
      Cont tailWindow modulus tailRead ->
        Cont tailRead tolerance toleranceRead ->
          Cont toleranceRead sealRow sealRead ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
                      hsame row tailRead ∨ hsame row toleranceRead ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont tailWindow modulus tailRead ∧
                      Cont tailRead tolerance toleranceRead ∧
                        Cont toleranceRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory tailRead ∧ UnaryHistory toleranceRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier tailRoute toleranceRoute sealRoute sealPkg
  obtain ⟨tailWindowUnary, modulusUnary, toleranceUnary, _ledgerUnary, sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailWindowModulus,
    _modulusTolerance, _ledgerSeal, _routesNameCert, _provenancePkg⟩ := carrier
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed tailWindowUnary modulusUnary tailRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed tailReadUnary toleranceUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
              hsame row tailRead ∨ hsame row toleranceRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tailWindow modulus tailRead ∧
              Cont tailRead tolerance toleranceRead ∧ Cont toleranceRead sealRow sealRead ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, tailRoute, toleranceRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, tailReadUnary, toleranceReadUnary, sealReadUnary⟩

end BEDC.Derived.CauchyOscillationUp
