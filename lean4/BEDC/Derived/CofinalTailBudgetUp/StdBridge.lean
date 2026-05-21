import BEDC.Derived.CofinalTailBudgetUp.NameCertObligations

namespace BEDC.Derived.CofinalTailBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CofinalTailBudgetUp_StdBridge [AskSetup] [PackageSetup]
    {budget windows readback sealRow transports routes provenance name bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CofinalTailBudgetCarrier budget windows readback sealRow transports routes provenance name
        bundle pkg →
      Cont routes provenance bridgeRead →
        PkgSig bundle bridgeRead pkg →
          UnaryHistory budget ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
            UnaryHistory sealRow ∧ UnaryHistory routes ∧ UnaryHistory bridgeRead ∧
              Cont budget windows readback ∧ Cont readback sealRow routes ∧
                Cont routes provenance bridgeRead ∧ PkgSig bundle bridgeRead pkg ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                    (fun _row : BHist =>
                      Cont budget windows readback ∧ Cont readback sealRow routes ∧
                        Cont routes provenance bridgeRead)
                    (fun row : BHist => hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeProvenanceBridge bridgePkg
  obtain ⟨budgetUnary, windowsUnary, readbackUnary, sealUnary, _transportsUnary,
    routesUnary, provenanceUnary, _nameUnary, budgetWindowsReadback, readbackSealRoutes,
    _provenancePkg, _namePkg⟩ := carrier
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed routesUnary provenanceUnary routeProvenanceBridge
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
        (fun _row : BHist =>
          Cont budget windows readback ∧ Cont readback sealRow routes ∧
            Cont routes provenance bridgeRead)
        (fun row : BHist => hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row _source
      exact ⟨budgetWindowsReadback, readbackSealRoutes, routeProvenanceBridge⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, bridgePkg⟩
  }
  exact
    ⟨budgetUnary, windowsUnary, readbackUnary, sealUnary, routesUnary, bridgeUnary,
      budgetWindowsReadback, readbackSealRoutes, routeProvenanceBridge, bridgePkg, cert⟩

end BEDC.Derived.CofinalTailBudgetUp
