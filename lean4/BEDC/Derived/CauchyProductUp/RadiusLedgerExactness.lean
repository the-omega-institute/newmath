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

theorem CauchyProductPacket_radius_ledger_exactness [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name radiusLedger budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont radiusA radiusB radiusLedger ->
        Cont radiusLedger product budgetRead ->
          PkgSig bundle budgetRead pkg ->
            SemanticNameCert
              (fun row : BHist =>
                hsame row radiusLedger ∨ hsame row budgetRead ∨ hsame row product)
              (fun row : BHist =>
                hsame row radiusLedger ∨ hsame row budgetRead ∨ hsame row product)
              (fun row : BHist =>
                PkgSig bundle budgetRead pkg ∧
                  (hsame row radiusLedger ∨ hsame row budgetRead ∨ hsame row product))
              hsame ∧
              UnaryHistory radiusA ∧ UnaryHistory radiusB ∧ UnaryHistory radiusLedger ∧
                UnaryHistory product ∧ UnaryHistory budgetRead ∧
                  Cont radiusA radiusB radiusLedger ∧ Cont radiusLedger product budgetRead ∧
                    PkgSig bundle name pkg ∧ PkgSig bundle budgetRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet radiusRoute budgetRoute budgetPkg
  obtain ⟨_sourceAUnary, _sourceBUnary, _windowAUnary, _windowBUnary, radiusAUnary,
    radiusBUnary, observationAUnary, observationBUnary, _routesUnary, _ledgerUnary,
    _windowTransport, productRoute, _classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have radiusLedgerUnary : UnaryHistory radiusLedger :=
    unary_cont_closed radiusAUnary radiusBUnary radiusRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed radiusLedgerUnary productUnary budgetRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row radiusLedger ∨ hsame row budgetRead ∨ hsame row product)
        (fun row : BHist =>
          hsame row radiusLedger ∨ hsame row budgetRead ∨ hsame row product)
        (fun row : BHist =>
          PkgSig bundle budgetRead pkg ∧
            (hsame row radiusLedger ∨ hsame row budgetRead ∨ hsame row product))
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro radiusLedger (Or.inl (hsame_refl radiusLedger))
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
          intro _row _other sameRows sourceRow
          cases sameRows
          exact sourceRow
      }
      pattern_sound := by
        intro _row sourceRow
        exact sourceRow
      ledger_sound := by
        intro _row sourceRow
        exact ⟨budgetPkg, sourceRow⟩
    }
  exact
    ⟨cert, radiusAUnary, radiusBUnary, radiusLedgerUnary, productUnary, budgetUnary,
      radiusRoute, budgetRoute, namePkg, budgetPkg⟩

theorem CauchyProductPacket_budget_public_handoff [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name budgetRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      Cont product ledger budgetRead ->
        Cont budgetRead routes publicRead ->
          PkgSig bundle publicRead pkg ->
            UnaryHistory sourceA ∧ UnaryHistory sourceB ∧ UnaryHistory windowA ∧
              UnaryHistory windowB ∧ UnaryHistory product ∧ UnaryHistory classifier ∧
                UnaryHistory budgetRead ∧ UnaryHistory publicRead ∧
                  Cont observationA observationB product ∧ Cont product ledger classifier ∧
                    Cont product ledger budgetRead ∧ Cont budgetRead routes publicRead ∧
                      PkgSig bundle name pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet budgetRoute publicRoute publicPkg
  obtain ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed productUnary ledgerUnary budgetRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed budgetUnary routesUnary publicRoute
  exact
    ⟨sourceAUnary, sourceBUnary, windowAUnary, windowBUnary, productUnary, classifierUnary,
      budgetUnary, publicUnary, productRoute, classifierRoute, budgetRoute, publicRoute,
      namePkg, publicPkg⟩

end BEDC.Derived.CauchyProductUp
