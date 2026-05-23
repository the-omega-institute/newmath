import BEDC.Derived.UniformModulusUp

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformModulusPacket_compact_continuous_handoff [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow compactRead pointwiseRead uniformRead exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      UnaryHistory pointwise ->
        Cont bundleRow radius compactRead ->
          Cont compactRead pointwise pointwiseRead ->
            Cont pointwiseRead foldLedger uniformRead ->
              Cont uniformRead nameRow exported ->
                PkgSig bundle exported pkg ->
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row exported ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                    (fun row : BHist =>
                      Cont uniformRead nameRow row ∧ Cont compactRead pointwise pointwiseRead ∧
                        Cont pointwiseRead foldLedger uniformRead)
                    (fun row : BHist =>
                      PkgSig bundle row pkg ∧ Cont bundleRow radius compactRead ∧
                        Cont precision radius foldLedger)
                    (fun row row' : BHist => hsame row row') := by
  intro packet pointwiseUnary compactRoute pointwiseRoute uniformRoute exportRoute exportPkg
  obtain ⟨_toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    _coverageRoute, _transportRoute, precisionRadiusFoldLedger, _foldNameProvenance,
    _provenancePkg⟩ := packet
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleRowUnary radiusUnary compactRoute
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed compactReadUnary pointwiseUnary pointwiseRoute
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary precisionRadiusFoldLedger
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed pointwiseReadUnary foldLedgerUnary uniformRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed uniformReadUnary nameRowUnary exportRoute
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
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨cont_result_hsame_transport exportRoute (hsame_symm source.left),
          pointwiseRoute, uniformRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, compactRoute, precisionRadiusFoldLedger⟩
  }

end BEDC.Derived.UniformModulusUp
