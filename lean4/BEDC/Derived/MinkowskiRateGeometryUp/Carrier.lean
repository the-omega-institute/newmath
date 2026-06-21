import BEDC.Derived.MinkowskiRateGeometryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MinkowskiRateGeometryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MinkowskiRateGeometryCarrier [AskSetup] [PackageSetup]
    (config causal rate frame distance transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory config ∧ UnaryHistory causal ∧ UnaryHistory rate ∧ UnaryHistory frame ∧
    UnaryHistory distance ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont config causal rate ∧
        Cont rate frame distance ∧ PkgSig bundle distance pkg

theorem MinkowskiRateGeometryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {config causal rate frame distance transport replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MinkowskiRateGeometryCarrier config causal rate frame distance transport replay provenance
        localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row distance ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row distance ∨ hsame row transport ∨ hsame row replay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont config causal rate ∧ Cont rate frame distance ∧
              PkgSig bundle distance pkg)
          hsame ∧ UnaryHistory distance := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier
  obtain ⟨_configUnary, _causalUnary, _rateUnary, _frameUnary, distanceUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, configCausalRate, rateFrameDistance,
    distancePkg⟩ := carrier
  have sourceDistance :
      (fun row : BHist => hsame row distance ∧ UnaryHistory row) distance := by
    exact ⟨hsame_refl distance, distanceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row distance ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row distance ∨ hsame row transport ∨ hsame row replay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont config causal rate ∧ Cont rate frame distance ∧
              PkgSig bundle distance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro distance sourceDistance
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inl sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, configCausalRate, rateFrameDistance, distancePkg⟩
  }
  exact ⟨cert, distanceUnary⟩

theorem MinkowskiRateGeometrySymmetry [AskSetup] [PackageSetup]
    {config causal rate frame distance transport replay provenance localName
      mirroredDistance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MinkowskiRateGeometryCarrier config causal rate frame distance transport replay provenance
        localName bundle pkg ->
      Cont frame rate mirroredDistance ->
        PkgSig bundle mirroredDistance pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row mirroredDistance ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row distance ∨ hsame row mirroredDistance ∨ hsame row frame ∨
                  hsame row rate)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont config causal rate ∧ Cont rate frame distance ∧
                  Cont frame rate mirroredDistance ∧ PkgSig bundle distance pkg ∧
                    PkgSig bundle mirroredDistance pkg)
              hsame ∧ UnaryHistory mirroredDistance := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier frameRateMirrored mirroredPkg
  obtain ⟨_configUnary, _causalUnary, rateUnary, frameUnary, _distanceUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, configCausalRate,
    rateFrameDistance, distancePkg⟩ := carrier
  have mirroredUnary : UnaryHistory mirroredDistance :=
    unary_cont_closed frameUnary rateUnary frameRateMirrored
  have sourceMirrored :
      (fun row : BHist => hsame row mirroredDistance ∧ UnaryHistory row)
          mirroredDistance := by
    exact ⟨hsame_refl mirroredDistance, mirroredUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row mirroredDistance ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row distance ∨ hsame row mirroredDistance ∨ hsame row frame ∨
              hsame row rate)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont config causal rate ∧ Cont rate frame distance ∧
              Cont frame rate mirroredDistance ∧ PkgSig bundle distance pkg ∧
                PkgSig bundle mirroredDistance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro mirroredDistance sourceMirrored
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inl sourceRow.left)
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, configCausalRate, rateFrameDistance, frameRateMirrored,
          distancePkg, mirroredPkg⟩
  }
  exact ⟨cert, mirroredUnary⟩

end BEDC.Derived.MinkowskiRateGeometryUp
