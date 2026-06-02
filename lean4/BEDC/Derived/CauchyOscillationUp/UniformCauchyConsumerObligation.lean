import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCarrier_uniform_cauchy_consumer_obligation [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert budgetRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg ->
      Cont modulus tolerance budgetRead ->
        Cont budgetRead ledger routes ->
          Cont routes sealRow sealRead ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
                        hsame row ledger ∨ hsame row budgetRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont modulus tolerance budgetRead ∧
                        Cont budgetRead ledger routes ∧ Cont routes sealRow sealRead ∧
                          PkgSig bundle sealRead pkg)
                    hsame ∧
                UnaryHistory budgetRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier budgetRoute routeReplay sealRoute sealPkg
  obtain ⟨_tailWindowUnary, modulusUnary, toleranceUnary, ledgerUnary, sealUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailModulusTolerance,
    _modulusToleranceLedger, _ledgerSealRoutes, _routesNameCert, _provenancePkg⟩ := carrier
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed modulusUnary toleranceUnary budgetRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed budgetUnary ledgerUnary routeReplay
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed routesUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
              hsame row ledger ∨ hsame row budgetRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont modulus tolerance budgetRead ∧
              Cont budgetRead ledger routes ∧ Cont routes sealRow sealRead ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead ⟨hsame_refl budgetRead, budgetUnary⟩
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
      right
      right
      right
      right
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, budgetRoute, routeReplay, sealRoute, sealPkg⟩
  }
  exact ⟨cert, budgetUnary, sealReadUnary⟩

end BEDC.Derived.CauchyOscillationUp
