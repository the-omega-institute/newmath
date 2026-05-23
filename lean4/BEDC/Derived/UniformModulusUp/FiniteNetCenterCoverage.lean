import BEDC.Derived.UniformModulusUp

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformModulusPacket_finite_net_center_coverage_obligation [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow center coverageRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      Cont bundleRow radius center ->
        Cont center coverage coverageRead ->
          Cont coverageRead nameRow exported ->
            PkgSig bundle exported pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row exported ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                  (fun row : BHist =>
                    Cont coverageRead nameRow row ∧ Cont bundleRow radius center)
                  (fun row : BHist =>
                    PkgSig bundle row pkg ∧ Cont center coverage coverageRead)
                  hsame ∧
                UnaryHistory center ∧ UnaryHistory coverageRead ∧
                  Cont center coverage coverageRead ∧ PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro packet centerRoute coverageReadRoute exportRoute exportPkg
  obtain ⟨toleranceUnary, _precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    coverageRoute, _transportRoute, _foldRoute, _provenanceRoute, _packetPkg⟩ := packet
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed toleranceUnary bundleRowUnary coverageRoute
  have centerUnary : UnaryHistory center :=
    unary_cont_closed bundleRowUnary radiusUnary centerRoute
  have coverageReadUnary : UnaryHistory coverageRead :=
    unary_cont_closed centerUnary coverageUnary coverageReadRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed coverageReadUnary nameRowUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exported ∧ UnaryHistory row ∧
            PkgSig bundle row pkg)
          (fun row : BHist => Cont coverageRead nameRow row ∧
            Cont bundleRow radius center)
          (fun row : BHist => PkgSig bundle row pkg ∧
            Cont center coverage coverageRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro exported ⟨hsame_refl exported, exportedUnary, exportPkg⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _row' sameRows sourceRow
          cases sameRows
          exact sourceRow
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨cont_result_hsame_transport exportRoute (hsame_symm sourceRow.left),
            centerRoute⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right.right, coverageReadRoute⟩
    }
  exact ⟨cert, centerUnary, coverageReadUnary, coverageReadRoute, exportPkg⟩

end BEDC.Derived.UniformModulusUp
