import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyModulusNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyModulusNormalizerCarrier [AskSetup] [PackageSetup]
    (x y muX muY meet window dyadic readback sealRow transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg hsame UnaryHistory
  UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory muX ∧ UnaryHistory muY ∧
    UnaryHistory meet ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
      UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
        UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont muX muY meet ∧ Cont meet window dyadic ∧ Cont dyadic readback sealRow ∧
            Cont sealRow transport route ∧ Cont route provenance name ∧
              PkgSig bundle meet pkg ∧ PkgSig bundle name pkg

theorem RegularCauchyModulusNormalizerCarrier_source_exposure_obligation [AskSetup]
    [PackageSetup]
    {x y muX muY meet window dyadic readback sealRow transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback sealRow
        transport route provenance name bundle pkg ->
      PkgSig bundle meet pkg ->
        SemanticNameCert
            (fun row : BHist =>
              RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                  sealRow transport route provenance name bundle pkg ∧
                hsame row meet)
            (fun row : BHist => hsame row meet ∧ UnaryHistory row)
            (fun _row : BHist =>
              UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory muX ∧ UnaryHistory muY ∧
                Cont muX muY meet ∧ PkgSig bundle meet pkg)
            hsame ∧
          UnaryHistory meet := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier meetPkg
  have carrierWitness := carrier
  obtain ⟨xUnary, yUnary, muXUnary, muYUnary, meetUnary, _windowUnary, _dyadicUnary,
    _readbackUnary, _sealUnary, _transportUnary, _routeUnary, _provenanceUnary, _nameUnary,
    sourceMeet, _meetWindowDyadic, _dyadicReadbackSeal, _sealTransportRoute,
    _routeProvenanceName, _carrierMeetPkg, _namePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusNormalizerCarrier x y muX muY meet window dyadic readback
                sealRow transport route provenance name bundle pkg ∧
              hsame row meet)
          (fun row : BHist => hsame row meet ∧ UnaryHistory row)
          (fun _row : BHist =>
            UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory muX ∧ UnaryHistory muY ∧
              Cont muX muY meet ∧ PkgSig bundle meet pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro meet (And.intro carrierWitness (hsame_refl meet))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same sourceRow
          exact And.intro sourceRow.left (hsame_trans (hsame_symm same) sourceRow.right)
      }
      pattern_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, unary_transport meetUnary sourceRow.right.symm⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨xUnary, yUnary, muXUnary, muYUnary, sourceMeet, meetPkg⟩
    }
  exact ⟨cert, meetUnary⟩

end BEDC.Derived.RegularCauchyModulusNormalizerUp
