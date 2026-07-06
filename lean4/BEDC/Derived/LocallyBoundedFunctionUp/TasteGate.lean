import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocallyBoundedFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocallyBoundedFunctionCarrier [AskSetup] [PackageSetup]
    (K F V B W R D A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory V ∧ UnaryHistory B ∧
    UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory A ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        Cont K F V ∧ Cont W R D ∧ Cont D A C ∧ PkgSig bundle P pkg

theorem LocallyBoundedFunctionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K F V B W R D A H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocallyBoundedFunctionCarrier K F V B W R D A H C P N bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            LocallyBoundedFunctionCarrier K F V B W R D A H C P row bundle pkg)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F V ∧ PkgSig bundle P pkg)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R D ∧ Cont D A C ∧ PkgSig bundle P pkg)
          hsame ∧
        Cont K F V ∧ Cont W R D ∧ Cont D A C ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  have carrierWitness := carrier
  obtain ⟨kUnary, fUnary, vUnary, bUnary, wUnary, rUnary, dUnary, aUnary, hUnary,
    cUnary, pUnary, nUnary, sourceRoute, boundRoute, sealRoute, provenancePkg⟩ :=
      carrier
  have sourceWitness :
      (fun row : BHist =>
        LocallyBoundedFunctionCarrier K F V B W R D A H C P row bundle pkg) N := by
    exact carrierWitness
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            LocallyBoundedFunctionCarrier K F V B W R D A H C P row bundle pkg)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F V ∧ PkgSig bundle P pkg)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R D ∧ Cont D A C ∧ PkgSig bundle P pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N sourceWitness
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' same
          exact hsame_symm same
        equiv_trans := by
          intro _row _row' _row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same sourceRow
          obtain ⟨sourceKUnary, sourceFUnary, sourceVUnary, sourceBUnary, sourceWUnary,
            sourceRUnary, sourceDUnary, sourceAUnary, sourceHUnary, sourceCUnary,
            sourcePUnary, sourceRowUnary, sourceRouteRow, boundRouteRow, sealRouteRow,
            provenancePkgRow⟩ := sourceRow
          exact
            ⟨sourceKUnary, sourceFUnary, sourceVUnary, sourceBUnary, sourceWUnary,
              sourceRUnary, sourceDUnary, sourceAUnary, sourceHUnary, sourceCUnary,
              sourcePUnary, unary_transport sourceRowUnary same, sourceRouteRow,
              boundRouteRow, sealRouteRow, provenancePkgRow⟩
      }
      pattern_sound := by
        intro row sourceRow
        obtain ⟨_sourceKUnary, _sourceFUnary, _sourceVUnary, _sourceBUnary,
          _sourceWUnary, _sourceRUnary, _sourceDUnary, _sourceAUnary, _sourceHUnary,
          _sourceCUnary, _sourcePUnary, sourceRowUnary, sourceRouteRow,
          _boundRouteRow, _sealRouteRow, provenancePkgRow⟩ := sourceRow
        exact ⟨sourceRowUnary, sourceRouteRow, provenancePkgRow⟩
      ledger_sound := by
        intro row sourceRow
        obtain ⟨_sourceKUnary, _sourceFUnary, _sourceVUnary, _sourceBUnary,
          _sourceWUnary, _sourceRUnary, _sourceDUnary, _sourceAUnary, _sourceHUnary,
          _sourceCUnary, _sourcePUnary, sourceRowUnary, _sourceRouteRow,
          boundRouteRow, sealRouteRow, provenancePkgRow⟩ := sourceRow
        exact ⟨sourceRowUnary, boundRouteRow, sealRouteRow, provenancePkgRow⟩
    }
  exact ⟨cert, sourceRoute, boundRoute, sealRoute, provenancePkg⟩

theorem LocallyBoundedFunctionTasteGate_single_carrier_alignment [AskSetup] [PackageSetup]
    {K F V B W R D A H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocallyBoundedFunctionCarrier K F V B W R D A H C P N bundle pkg →
      Nonempty
          (NameCert
            (fun row : BHist =>
              LocallyBoundedFunctionCarrier K F V B W R D A H C P row bundle pkg)
            hsame) ∧
        Cont K F V ∧ Cont W R D ∧ Cont D A C ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg NameCert hsame Cont PkgSig
  intro carrier
  obtain ⟨kUnary, fUnary, vUnary, bUnary, wUnary, rUnary, dUnary, aUnary, hUnary,
    cUnary, pUnary, nUnary, sourceRoute, boundRoute, sealRoute, provenancePkg⟩ :=
      carrier
  have carrierWitness :
      (fun row : BHist =>
        LocallyBoundedFunctionCarrier K F V B W R D A H C P row bundle pkg) N := by
    exact
      ⟨kUnary, fUnary, vUnary, bUnary, wUnary, rUnary, dUnary, aUnary, hUnary,
        cUnary, pUnary, nUnary, sourceRoute, boundRoute, sealRoute, provenancePkg⟩
  have cert :
      NameCert
          (fun row : BHist =>
            LocallyBoundedFunctionCarrier K F V B W R D A H C P row bundle pkg)
          hsame := {
    carrier_inhabited := Exists.intro N carrierWitness
    equiv_refl := by
      intro row _source
      exact hsame_refl row
    equiv_symm := by
      intro _row _row' same
      exact hsame_symm same
    equiv_trans := by
      intro _row _row' _row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    carrier_respects_equiv := by
      intro row row' same sourceRow
      obtain ⟨sourceKUnary, sourceFUnary, sourceVUnary, sourceBUnary, sourceWUnary,
        sourceRUnary, sourceDUnary, sourceAUnary, sourceHUnary, sourceCUnary,
        sourcePUnary, sourceRowUnary, sourceRouteRow, boundRouteRow, sealRouteRow,
        provenancePkgRow⟩ := sourceRow
      exact
        ⟨sourceKUnary, sourceFUnary, sourceVUnary, sourceBUnary, sourceWUnary,
          sourceRUnary, sourceDUnary, sourceAUnary, sourceHUnary, sourceCUnary,
          sourcePUnary, unary_transport sourceRowUnary same, sourceRouteRow,
          boundRouteRow, sealRouteRow, provenancePkgRow⟩
  }
  exact ⟨⟨cert⟩, sourceRoute, boundRoute, sealRoute, provenancePkg⟩

end BEDC.Derived.LocallyBoundedFunctionUp
