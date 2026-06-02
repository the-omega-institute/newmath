import BEDC.Derived.CauchyOscillationUp

namespace BEDC.Derived.CauchyOscillationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyOscillationCompletionFrontierPublicReadiness [AskSetup] [PackageSetup]
    {tailWindow modulus tolerance ledger sealRow transport routes provenance nameCert thresholdRead
      ledgerRead sealRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyOscillationCarrier tailWindow modulus tolerance ledger sealRow transport routes provenance
        nameCert bundle pkg →
      Cont tailWindow modulus thresholdRead →
        Cont thresholdRead tolerance ledgerRead →
          Cont ledgerRead sealRow sealRead →
            Cont sealRead transport replayRead →
              PkgSig bundle replayRead pkg →
                SemanticNameCert
                      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
                          hsame row ledgerRead ∨ hsame row sealRead ∨ hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont tailWindow modulus thresholdRead ∧
                          Cont thresholdRead tolerance ledgerRead ∧
                            Cont ledgerRead sealRow sealRead ∧
                              Cont sealRead transport replayRead ∧
                                PkgSig bundle replayRead pkg)
                      hsame ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: CauchyOscillationCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier thresholdRoute ledgerRoute sealRoute replayRoute replayPkg
  obtain ⟨tailWindowUnary, modulusUnary, toleranceUnary, _ledgerUnary, sealUnary,
    transportUnary, _routesUnary, _provenanceUnary, _nameCertUnary, _tailWindowModulus,
    _modulusTolerance, _ledgerSeal, _routesNameCert, provenancePkg⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed tailWindowUnary modulusUnary thresholdRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed thresholdUnary toleranceUnary ledgerRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed ledgerReadUnary sealUnary sealRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed sealReadUnary transportUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row tailWindow ∨ hsame row modulus ∨ hsame row tolerance ∨
              hsame row ledgerRead ∨ hsame row sealRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tailWindow modulus thresholdRead ∧
              Cont thresholdRead tolerance ledgerRead ∧ Cont ledgerRead sealRow sealRead ∧
                Cont sealRead transport replayRead ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayReadUnary⟩
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
      exact
        ⟨source.right, thresholdRoute, ledgerRoute, sealRoute, replayRoute, replayPkg⟩
  }
  exact ⟨cert, provenancePkg⟩

end BEDC.Derived.CauchyOscillationUp
