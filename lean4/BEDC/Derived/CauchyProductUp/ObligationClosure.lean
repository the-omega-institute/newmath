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

theorem CauchyProductPacket_obligation_closure [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name realSeal radiusLedger budgetRead regseqSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont classifier routes realSeal ->
        Cont radiusA radiusB radiusLedger ->
          Cont radiusLedger product budgetRead ->
            Cont budgetRead classifier regseqSeal ->
              PkgSig bundle realSeal pkg ->
                PkgSig bundle regseqSeal pkg ->
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                          hsame row ledger ∨ hsame row radiusLedger ∨
                            hsame row budgetRead ∨ hsame row regseqSeal)
                      (fun row : BHist =>
                        hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                          hsame row ledger ∨ hsame row radiusLedger ∨
                            hsame row budgetRead ∨ hsame row regseqSeal)
                      (fun row : BHist =>
                        PkgSig bundle name pkg ∧
                          (hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                            hsame row ledger ∨ hsame row radiusLedger ∨
                              hsame row budgetRead ∨ hsame row regseqSeal))
                      hsame ∧
                    UnaryHistory product ∧ UnaryHistory classifier ∧ UnaryHistory realSeal ∧
                      UnaryHistory radiusLedger ∧ UnaryHistory budgetRead ∧
                        UnaryHistory regseqSeal ∧ Cont observationA observationB product ∧
                          Cont product ledger classifier ∧ Cont classifier routes realSeal ∧
                            Cont radiusA radiusB radiusLedger ∧
                              Cont radiusLedger product budgetRead ∧
                                Cont budgetRead classifier regseqSeal ∧
                                  PkgSig bundle name pkg ∧ PkgSig bundle realSeal pkg ∧
                                    PkgSig bundle regseqSeal pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro packet classifierReal radiusRoute budgetRoute regseqRoute realSealPkg regseqSealPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed classifierUnary routesUnary classifierReal
  have radiusLedgerUnary : UnaryHistory radiusLedger :=
    unary_cont_closed radiusAUnary radiusBUnary radiusRoute
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed radiusLedgerUnary productUnary budgetRoute
  have regseqSealUnary : UnaryHistory regseqSeal :=
    unary_cont_closed budgetReadUnary classifierUnary regseqRoute
  have sourceAtProduct :
      hsame product product ∨ hsame product classifier ∨ hsame product realSeal ∨
        hsame product ledger ∨ hsame product radiusLedger ∨ hsame product budgetRead ∨
          hsame product regseqSeal :=
    Or.inl (hsame_refl product)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
              hsame row ledger ∨ hsame row radiusLedger ∨ hsame row budgetRead ∨
                hsame row regseqSeal)
          (fun row : BHist =>
            hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
              hsame row ledger ∨ hsame row radiusLedger ∨ hsame row budgetRead ∨
                hsame row regseqSeal)
          (fun row : BHist =>
            PkgSig bundle name pkg ∧
              (hsame row product ∨ hsame row classifier ∨ hsame row realSeal ∨
                hsame row ledger ∨ hsame row radiusLedger ∨ hsame row budgetRead ∨
                  hsame row regseqSeal))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro product sourceAtProduct
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨namePkg, source⟩
  }
  exact
    ⟨cert, productUnary, classifierUnary, realSealUnary, radiusLedgerUnary,
      budgetReadUnary, regseqSealUnary, productRoute, classifierRoute, classifierReal,
      radiusRoute, budgetRoute, regseqRoute, namePkg, realSealPkg, regseqSealPkg⟩

end BEDC.Derived.CauchyProductUp
