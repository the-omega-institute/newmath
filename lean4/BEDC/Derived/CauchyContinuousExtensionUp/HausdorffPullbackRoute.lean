import BEDC.Derived.CauchyContinuousExtensionUp.RegularTailTransport
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyContinuousExtensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyContinuousExtensionCarrier_hausdorff_pullback_route [AskSetup] [PackageSetup]
    {source window dyadic map extension ledger transport replay provenance localName sourceWindow
      windowDyadic dyadicMap mapExtension extensionLedger hausdorffWitness : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousExtensionCarrier source window dyadic map extension ledger transport replay
        provenance localName bundle pkg →
      Cont source window sourceWindow →
        Cont sourceWindow dyadic windowDyadic →
          Cont windowDyadic map dyadicMap →
            Cont dyadicMap extension mapExtension →
              Cont mapExtension ledger extensionLedger →
                Cont extensionLedger transport hausdorffWitness →
                  PkgSig bundle provenance pkg →
                    PkgSig bundle hausdorffWitness pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row hausdorffWitness ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row source ∨ hsame row window ∨ hsame row dyadic ∨
                              hsame row map ∨ hsame row extension ∨ hsame row ledger ∨
                                hsame row transport ∨ hsame row hausdorffWitness)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle hausdorffWitness pkg)
                          hsame ∧
                        UnaryHistory sourceWindow ∧ UnaryHistory windowDyadic ∧
                          UnaryHistory dyadicMap ∧ UnaryHistory mapExtension ∧
                            UnaryHistory extensionLedger ∧
                              UnaryHistory hausdorffWitness := by
  -- BEDC touchpoint anchor: CauchyContinuousExtensionCarrier BHist ProbeBundle Pkg Cont
  -- hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute windowRoute dyadicRoute mapRoute extensionRoute hausdorffRoute
    provenancePkg hausdorffPkg
  obtain ⟨sourceUnary, windowUnary, dyadicUnary, mapUnary, extensionUnary, ledgerUnary,
    transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _carrierProvenancePkg,
    _carrierLocalNamePkg⟩ := carrier
  have sourceWindowUnary : UnaryHistory sourceWindow :=
    unary_cont_closed sourceUnary windowUnary sourceRoute
  have windowDyadicUnary : UnaryHistory windowDyadic :=
    unary_cont_closed sourceWindowUnary dyadicUnary windowRoute
  have dyadicMapUnary : UnaryHistory dyadicMap :=
    unary_cont_closed windowDyadicUnary mapUnary dyadicRoute
  have mapExtensionUnary : UnaryHistory mapExtension :=
    unary_cont_closed dyadicMapUnary extensionUnary mapRoute
  have extensionLedgerUnary : UnaryHistory extensionLedger :=
    unary_cont_closed mapExtensionUnary ledgerUnary extensionRoute
  have hausdorffUnary : UnaryHistory hausdorffWitness :=
    unary_cont_closed extensionLedgerUnary transportUnary hausdorffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row hausdorffWitness ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row window ∨ hsame row dyadic ∨ hsame row map ∨
              hsame row extension ∨ hsame row ledger ∨ hsame row transport ∨
                hsame row hausdorffWitness)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle hausdorffWitness pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro hausdorffWitness ⟨hsame_refl hausdorffWitness, hausdorffUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, hausdorffPkg⟩
  }
  exact
    ⟨cert, sourceWindowUnary, windowDyadicUnary, dyadicMapUnary, mapExtensionUnary,
      extensionLedgerUnary, hausdorffUnary⟩

end BEDC.Derived.CauchyContinuousExtensionUp
