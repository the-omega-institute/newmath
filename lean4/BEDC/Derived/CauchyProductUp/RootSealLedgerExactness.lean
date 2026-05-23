import BEDC.Derived.CauchyProductUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyProductUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyProductPacket_root_seal_ledger_exactness [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetClassifier budgetSeal sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes budgetClassifier ->
        Cont budgetClassifier ledger budgetSeal ->
          Cont budgetSeal routes sealRead ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row ledger ∧ UnaryHistory row ∧
                      Cont classifier routes budgetClassifier ∧
                        Cont budgetClassifier ledger budgetSeal ∧
                          Cont budgetSeal routes sealRead ∧ PkgSig bundle name pkg)
                  (fun row : BHist => hsame row ledger ∧ Cont budgetSeal routes sealRead)
                  (fun row : BHist => hsame row ledger ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory budgetSeal ∧
                  UnaryHistory sealRead ∧ Cont product ledger classifier ∧
                    Cont budgetSeal routes sealRead ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet classifierBudget budgetSealRoute sealReadRoute sealReadPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetClassifierUnary : UnaryHistory budgetClassifier :=
    unary_cont_closed classifierUnary routesUnary classifierBudget
  have budgetSealUnary : UnaryHistory budgetSeal :=
    unary_cont_closed budgetClassifierUnary ledgerUnary budgetSealRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed budgetSealUnary routesUnary sealReadRoute
  have sourceAtLedger :
      hsame ledger ledger ∧ UnaryHistory ledger ∧
        Cont classifier routes budgetClassifier ∧
          Cont budgetClassifier ledger budgetSeal ∧
            Cont budgetSeal routes sealRead ∧ PkgSig bundle name pkg :=
    ⟨hsame_refl ledger, ledgerUnary, classifierBudget, budgetSealRoute, sealReadRoute,
      namePkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row ledger ∧ UnaryHistory row ∧ Cont classifier routes budgetClassifier ∧
              Cont budgetClassifier ledger budgetSeal ∧ Cont budgetSeal routes sealRead ∧
                PkgSig bundle name pkg)
          (fun row : BHist => hsame row ledger ∧ Cont budgetSeal routes sealRead)
          (fun row : BHist => hsame row ledger ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledger sourceAtLedger
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
        intro row row' sameRows source
        obtain ⟨sameLedger, rowUnary, rowClassifierBudget, rowBudgetSealRoute,
          rowSealReadRoute, rowNamePkg⟩ := source
        exact
          ⟨hsame_trans (hsame_symm sameRows) sameLedger,
            unary_transport rowUnary sameRows, rowClassifierBudget, rowBudgetSealRoute,
            rowSealReadRoute, rowNamePkg⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, source.right.right.right.right.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sealReadPkg⟩
  }
  exact
    ⟨cert, productUnary, classifierUnary, budgetSealUnary, sealReadUnary, classifierRoute,
      sealReadRoute, sealReadPkg⟩

end BEDC.Derived.CauchyProductUp
