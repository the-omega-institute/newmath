import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HausdorffMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HausdorffMetricCarrier [AskSetup] [PackageSetup]
    (subsetA subsetB metric compactRows finiteNets distanceRows symmetricBounds transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory subsetA ∧ UnaryHistory subsetB ∧ UnaryHistory metric ∧
    UnaryHistory compactRows ∧ UnaryHistory finiteNets ∧ UnaryHistory distanceRows ∧
      UnaryHistory symmetricBounds ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont subsetA subsetB metric ∧ Cont compactRows finiteNets distanceRows ∧
            Cont distanceRows symmetricBounds replay ∧ PkgSig bundle provenance pkg

theorem HausdorffMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {subsetA subsetB metric compactRows finiteNets distanceRows symmetricBounds transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HausdorffMetricCarrier subsetA subsetB metric compactRows finiteNets distanceRows
        symmetricBounds transport replay provenance localName bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          HausdorffMetricCarrier subsetA subsetB metric compactRows finiteNets distanceRows
            symmetricBounds transport replay provenance localName bundle pkg ∧
              hsame row localName)
        (fun row : BHist =>
          hsame row localName ∧ Cont subsetA subsetB metric ∧
            Cont compactRows finiteNets distanceRows ∧
              Cont distanceRows symmetricBounds replay)
        (fun row : BHist =>
          hsame row localName ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert Cont UnaryHistory
  intro carrier
  let carrierSource := carrier
  obtain ⟨_subsetAUnary, _subsetBUnary, _metricUnary, _compactRowsUnary,
    _finiteNetsUnary, _distanceRowsUnary, _symmetricBoundsUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, subsetMetricRoute,
    netDistanceRoute, distanceReplayRoute, provenancePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨carrierSource, hsame_refl localName⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.right, subsetMetricRoute, netDistanceRoute, distanceReplayRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg⟩
  }

end BEDC.Derived.HausdorffMetricUp
