import BEDC.Derived.UniformModulusUp

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformModulusPacket_precision_consumer_nonescape [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow pointwiseRead precisionConsumer exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      UnaryHistory pointwise ->
        Cont bundleRow radius pointwiseRead ->
          Cont pointwiseRead foldLedger precisionConsumer ->
            Cont precisionConsumer nameRow exported ->
              PkgSig bundle exported pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row exported ∧ UnaryHistory row)
                  (fun row : BHist => hsame row precisionConsumer ∨ hsame row exported)
                  (fun row : BHist =>
                    hsame row exported ∧ PkgSig bundle exported pkg ∧
                      Cont pointwiseRead foldLedger precisionConsumer)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro packet pointwiseUnary pointwiseRoute consumerRoute exportRoute exportPkg
  obtain ⟨_toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    _coverageRoute, _transportRoute, foldRoute, _provenanceRoute, _packetPkg⟩ := packet
  have pointwiseReadUnary : UnaryHistory pointwiseRead :=
    unary_cont_closed bundleRowUnary radiusUnary pointwiseRoute
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary foldRoute
  have precisionConsumerUnary : UnaryHistory precisionConsumer :=
    unary_cont_closed pointwiseReadUnary foldLedgerUnary consumerRoute
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed precisionConsumerUnary nameRowUnary exportRoute
  exact {
    core := {
      carrier_inhabited := Exists.intro exported ⟨hsame_refl exported, exportedUnary⟩
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
        exact ⟨hsame_trans (hsame_symm same) sourceRow.left,
          unary_transport sourceRow.right same⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, exportPkg, consumerRoute⟩
  }

end BEDC.Derived.UniformModulusUp
