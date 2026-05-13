import BEDC.Derived.UniformModulusUp

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformModulusPacket_root_compact_continuous_threshold [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow compactRead pointwiseRead threshold exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      UnaryHistory pointwise ->
        Cont bundleRow radius compactRead ->
          Cont compactRead pointwise pointwiseRead ->
            Cont pointwiseRead foldLedger threshold ->
              Cont threshold nameRow exported ->
                PkgSig bundle exported pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row exported ∧ UnaryHistory row ∧
                      PkgSig bundle row pkg)
                    (fun row : BHist => Cont threshold nameRow row ∧
                      Cont compactRead pointwise pointwiseRead ∧
                        Cont pointwiseRead foldLedger threshold)
                    (fun row : BHist => PkgSig bundle row pkg ∧
                      Cont precision radius foldLedger ∧ Cont threshold nameRow exported)
                    (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro packet pointwiseUnary compactRoute pointwiseRoute thresholdRoute exportRoute exportPkg
  obtain ⟨_toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    _coverageRoute, _transportRoute, precisionRadiusFoldLedger, _foldNameProvenance,
    _provenancePkg⟩ := packet
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleRowUnary radiusUnary compactRoute
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed compactReadUnary pointwiseUnary pointwiseRoute
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary precisionRadiusFoldLedger
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed pointwiseReadUnary foldLedgerUnary thresholdRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed thresholdUnary nameRowUnary exportRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro exported ⟨hsame_refl exported, exportedUnary, exportPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same sourceRow
        cases same
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨cont_result_hsame_transport exportRoute (hsame_symm sourceRow.left),
          pointwiseRoute, thresholdRoute⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, precisionRadiusFoldLedger, exportRoute⟩
  }

theorem UniformModulusPacket_root_net_minimum_row [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow threshold exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      Cont precision radius threshold ->
        Cont threshold nameRow exported ->
          PkgSig bundle exported pkg ->
            UnaryHistory precision ∧ UnaryHistory radius ∧ UnaryHistory foldLedger ∧
              UnaryHistory threshold ∧ UnaryHistory exported ∧ hsame foldLedger threshold ∧
                Cont precision radius threshold ∧ Cont threshold nameRow exported ∧
                  PkgSig bundle exported pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg hsame
  intro packet thresholdRoute exportRoute exportPkg
  obtain ⟨_toleranceUnary, precisionUnary, _bundleRowUnary, radiusUnary, nameRowUnary,
    _coverageRoute, _transportRoute, packetFoldRoute, _provenanceRoute, _provenancePkg⟩ :=
    packet
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary packetFoldRoute
  have thresholdUnary : UnaryHistory threshold :=
    unary_cont_closed precisionUnary radiusUnary thresholdRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed thresholdUnary nameRowUnary exportRoute
  have sameFoldThreshold : hsame foldLedger threshold :=
    hsame_symm (cont_deterministic thresholdRoute packetFoldRoute)
  exact
    ⟨precisionUnary, radiusUnary, foldLedgerUnary, thresholdUnary, exportedUnary,
      sameFoldThreshold, thresholdRoute, exportRoute, exportPkg⟩

end BEDC.Derived.UniformModulusUp
