import BEDC.Derived.BaireUltrametricUp.TasteGate
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BaireUltrametricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BaireUltrametricCarrier [AskSetup] [PackageSetup]
    (bairePrefix metric ultra window transport replay provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory bairePrefix ∧ UnaryHistory metric ∧ UnaryHistory ultra ∧
    UnaryHistory window ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory nameCert ∧ Cont bairePrefix window metric ∧
        Cont metric ultra replay ∧ PkgSig bundle provenance pkg ∧
          PkgSig bundle nameCert pkg

theorem BaireUltrametricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {bairePrefix metric ultra window transport replay provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireUltrametricCarrier bairePrefix metric ultra window transport replay provenance
        nameCert bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row nameCert ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bairePrefix ∨ hsame row metric ∨ hsame row ultra ∨
              hsame row window ∨ hsame row transport ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bairePrefix window metric ∧ Cont metric ultra replay ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg)
          hsame ∧
        Cont bairePrefix window metric ∧ Cont metric ultra replay ∧
          PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier
  obtain ⟨_prefixUnary, _metricUnary, _ultraUnary, _windowUnary, _transportUnary,
    _replayUnary, _provenanceUnary, nameCertUnary, prefixMetricRoute, ultrametricReplayRoute,
    provenancePkg, nameCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameCert ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row bairePrefix ∨ hsame row metric ∨ hsame row ultra ∨
              hsame row window ∨ hsame row transport ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont bairePrefix window metric ∧ Cont metric ultra replay ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg)
          hsame := by
    exact
      { core :=
          { carrier_inhabited := Exists.intro nameCert ⟨hsame_refl nameCert, nameCertUnary⟩
            equiv_refl := by
              intro h _source
              exact hsame_refl h
            equiv_symm := by
              intro _h _k same
              exact hsame_symm same
            equiv_trans := by
              intro _h _k _r sameHK sameKR
              exact hsame_trans sameHK sameKR
            carrier_respects_equiv := by
              intro _h _k same source
              exact
                ⟨hsame_trans (hsame_symm same) source.left,
                  unary_transport source.right same⟩ }
        pattern_sound := by
          intro _row source
          right
          right
          right
          right
          right
          right
          right
          exact source.left
        ledger_sound := by
          intro _row source
          exact
            ⟨source.right, prefixMetricRoute, ultrametricReplayRoute, provenancePkg,
              nameCertPkg⟩ }
  exact ⟨cert, prefixMetricRoute, ultrametricReplayRoute, nameCertPkg⟩

end BEDC.Derived.BaireUltrametricUp
