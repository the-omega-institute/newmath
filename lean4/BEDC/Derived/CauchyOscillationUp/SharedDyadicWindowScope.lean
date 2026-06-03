import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationSharedDyadicWindowScope [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert
      windowRead thresholdRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg ->
      Cont tailWindow modulus windowRead ->
        Cont windowRead tolerance thresholdRead ->
          Cont thresholdRead ledger toleranceRead ->
            Cont toleranceRead sealRow sealRead ->
              PkgSig bundle provenance pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
                        hsame row ledger ∨ hsame row windowRead ∨ hsame row thresholdRead ∨
                          hsame row toleranceRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont tailWindow modulus windowRead ∧
                        Cont windowRead tolerance thresholdRead ∧
                          Cont thresholdRead ledger toleranceRead ∧
                            Cont toleranceRead sealRow sealRead ∧
                              PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧ UnaryHistory thresholdRead ∧
                    UnaryHistory toleranceRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier windowRoute thresholdRoute toleranceRoute sealRoute provenancePkg
  obtain ⟨tailUnary, modulusUnary, toleranceUnary, ledgerUnary, sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _carrierWindow,
    _carrierLedger, _carrierRoutes, _carrierProvenance, _carrierPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed tailUnary modulusUnary windowRoute
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed windowUnary toleranceUnary thresholdRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed thresholdUnary ledgerUnary toleranceRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
              hsame row ledger ∨ hsame row windowRead ∨ hsame row thresholdRead ∨
                hsame row toleranceRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tailWindow modulus windowRead ∧
              Cont windowRead tolerance thresholdRead ∧
                Cont thresholdRead ledger toleranceRead ∧ Cont toleranceRead sealRow sealRead ∧
                  PkgSig bundle provenance pkg)
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, thresholdRoute, toleranceRoute, sealRoute,
          provenancePkg⟩
  }
  exact ⟨cert, windowUnary, thresholdUnary, toleranceReadUnary, sealReadUnary⟩

end BEDC.Derived.CauchyOscillationUp
