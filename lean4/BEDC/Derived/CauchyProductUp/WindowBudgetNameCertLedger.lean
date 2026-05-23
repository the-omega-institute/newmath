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

theorem CauchyProductPacket_window_budget_namecert_ledger [AskSetup] [PackageSetup]
    {sourceA sourceB windowA windowB radiusA radiusB observationA observationB product
      classifier transport routes ledger name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyProductPacket sourceA sourceB windowA windowB radiusA radiusB observationA
        observationB product classifier transport routes ledger name bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row ledger ∧ UnaryHistory row ∧ Cont observationA observationB product ∧
              Cont product ledger classifier ∧ PkgSig bundle name pkg)
          (fun row : BHist => hsame row ledger ∧ Cont observationA observationB product)
          (fun row : BHist => hsame row ledger ∧ PkgSig bundle name pkg)
          hsame ∧
        UnaryHistory windowA ∧ UnaryHistory windowB ∧ UnaryHistory product ∧
          UnaryHistory classifier ∧ Cont observationA observationB product ∧
            Cont product ledger classifier ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet
  obtain ⟨_sourceAUnary, _sourceBUnary, windowAUnary, windowBUnary, _radiusAUnary,
    _radiusBUnary, observationAUnary, observationBUnary, _routesUnary, ledgerUnary,
    _windowTransport, productRoute, classifierRoute, namePkg⟩ := packet
  have productUnary : UnaryHistory product :=
    unary_cont_closed observationAUnary observationBUnary productRoute
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed productUnary ledgerUnary classifierRoute
  have sourceAtLedger :
      hsame ledger ledger ∧ UnaryHistory ledger ∧ Cont observationA observationB product ∧
        Cont product ledger classifier ∧ PkgSig bundle name pkg :=
    ⟨hsame_refl ledger, ledgerUnary, productRoute, classifierRoute, namePkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row ledger ∧ UnaryHistory row ∧ Cont observationA observationB product ∧
              Cont product ledger classifier ∧ PkgSig bundle name pkg)
          (fun row : BHist => hsame row ledger ∧ Cont observationA observationB product)
          (fun row : BHist => hsame row ledger ∧ PkgSig bundle name pkg)
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
        obtain ⟨sameLedger, rowUnary, rowProductRoute, rowClassifierRoute, rowNamePkg⟩ :=
          source
        exact
          ⟨hsame_trans (hsame_symm sameRows) sameLedger,
            unary_transport rowUnary sameRows, rowProductRoute, rowClassifierRoute,
            rowNamePkg⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, source.right.right.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, source.right.right.right.right⟩
  }
  exact
    ⟨cert, windowAUnary, windowBUnary, productUnary, classifierUnary, productRoute,
      classifierRoute, namePkg⟩

end BEDC.Derived.CauchyProductUp
