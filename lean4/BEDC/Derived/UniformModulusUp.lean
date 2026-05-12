import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformModulusPacket [AskSetup] [PackageSetup]
    (tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory tolerance ∧ UnaryHistory precision ∧ UnaryHistory bundleRow ∧
    UnaryHistory radius ∧ UnaryHistory nameRow ∧
      Cont tolerance bundleRow coverage ∧ Cont coverage pointwise transport ∧
        Cont precision radius foldLedger ∧ Cont foldLedger nameRow provenance ∧
          PkgSig bundle provenance pkg

theorem UniformModulusPacket_finite_probe_bundle_fold [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow foldedExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      Cont precision radius foldLedger ->
        Cont foldLedger nameRow foldedExport ->
          PkgSig bundle foldedExport pkg ->
            UnaryHistory tolerance ∧ UnaryHistory precision ∧ UnaryHistory bundleRow ∧
              UnaryHistory radius ∧ UnaryHistory foldLedger ∧ UnaryHistory foldedExport ∧
                Cont precision radius foldLedger ∧ Cont foldLedger nameRow foldedExport ∧
                  PkgSig bundle foldedExport pkg := by
  intro packet foldRoute exportRoute exportPkg
  obtain ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    _coverageRoute, _transportRoute, _packetFoldRoute, _provenanceRoute, _provenancePkg⟩ :=
    packet
  have foldUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary foldRoute
  have exportUnary : UnaryHistory foldedExport :=
    unary_cont_closed foldUnary nameRowUnary exportRoute
  exact
    ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, foldUnary, exportUnary,
      foldRoute, exportRoute, exportPkg⟩

theorem UniformModulusPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {tolerance precision bundleRow radius coverage pointwise foldLedger transport provenance
      nameRow exported : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformModulusPacket tolerance precision bundleRow radius coverage pointwise foldLedger
        transport provenance nameRow bundle pkg ->
      Cont foldLedger nameRow exported ->
        PkgSig bundle exported pkg ->
          SemanticNameCert
            (fun row : BHist => hsame row exported ∧ UnaryHistory row ∧
              PkgSig bundle row pkg)
            (fun row : BHist => Cont foldLedger nameRow row ∧
              Cont tolerance bundleRow coverage ∧ Cont coverage pointwise transport)
            (fun row : BHist => PkgSig bundle row pkg ∧ Cont precision radius foldLedger ∧
              Cont foldLedger nameRow exported)
            (fun row row' : BHist => hsame row row') := by
  intro packet exportRoute exportPkg
  obtain ⟨toleranceUnary, precisionUnary, bundleRowUnary, radiusUnary, nameRowUnary,
    toleranceBundleCoverage, coveragePointwiseTransport, precisionRadiusFoldLedger,
    _foldNameProvenance, _provenancePkg⟩ := packet
  have foldLedgerUnary : UnaryHistory foldLedger :=
    unary_cont_closed precisionUnary radiusUnary precisionRadiusFoldLedger
  have exportedUnary : UnaryHistory exported :=
    unary_cont_closed foldLedgerUnary nameRowUnary exportRoute
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
          toleranceBundleCoverage, coveragePointwiseTransport⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, precisionRadiusFoldLedger, exportRoute⟩
  }

end BEDC.Derived.UniformModulusUp
