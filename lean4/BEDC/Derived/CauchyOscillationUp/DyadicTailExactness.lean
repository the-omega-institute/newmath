import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCarrier_dyadic_tail_exactness [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert ledgerRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg ->
      Cont modulus tolerance ledgerRead ->
        Cont ledgerRead sealRow sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                  (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
                      hsame row ledgerRead ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont modulus tolerance ledgerRead ∧
                      Cont ledgerRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
              UnaryHistory ledgerRead ∧ hsame ledger ledgerRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier ledgerRoute sealRoute sealPkg
  obtain ⟨_tailWindowUnary, modulusUnary, toleranceUnary, _ledgerUnary, sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailWindowModulus,
    carrierLedgerRoute, _ledgerSeal, _routesNameCert, _carrierPkg⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed modulusUnary toleranceUnary ledgerRoute
  have sameLedger : hsame ledger ledgerRead :=
    cont_respects_hsame (hsame_refl modulus) (hsame_refl tolerance) carrierLedgerRoute
      ledgerRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerReadUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
              hsame row ledgerRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus tolerance ledgerRead ∧
              Cont ledgerRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ledgerRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, ledgerReadUnary, sameLedger, sealReadUnary⟩

end BEDC.Derived.CauchyOscillationUp
