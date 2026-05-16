import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyModulusWitnessLedgerCarrier [AskSetup] [PackageSetup]
    (source witness window normalizer tail dyadic readback sealRow transport route provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory witness ∧ UnaryHistory window ∧
    UnaryHistory normalizer ∧ UnaryHistory tail ∧ UnaryHistory dyadic ∧
      UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
        UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          hsame transport BHist.Empty ∧ Cont witness window normalizer ∧
            Cont normalizer tail dyadic ∧ Cont dyadic readback sealRow ∧
              Cont transport route provenance ∧ hsame route sealRow ∧
                PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg

theorem RegularCauchyModulusWitnessLedgerCarrier_namecert_obligations [AskSetup]
    [PackageSetup]
    {source witness window normalizer tail dyadic readback sealRow transport route provenance
      name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
        readback sealRow transport route provenance name bundle pkg ->
      Cont sealRow transport endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail
                  dyadic readback sealRow transport route provenance name bundle pkg ∧
                    hsame row endpoint)
              (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
                  Cont dyadic readback sealRow ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sealTransportEndpoint endpointPkg
  have carrierWitness := carrier
  obtain ⟨_sourceUnary, witnessUnary, windowUnary, _normalizerUnary, tailUnary,
    _dyadicUnary, readbackUnary, sealUnary, transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, transportEmpty, witnessWindowNormalizer,
    normalizerTailDyadic, dyadicReadbackSeal, _transportRouteProvenance, _routeSeal,
    _provenancePkg, _namePkg⟩ := carrier
  have normalizerUnary : UnaryHistory normalizer :=
    unary_cont_closed witnessUnary windowUnary witnessWindowNormalizer
  have dyadicUnary : UnaryHistory dyadic :=
    unary_cont_closed normalizerUnary tailUnary normalizerTailDyadic
  have sealUnaryFromRoute : UnaryHistory sealRow :=
    unary_cont_closed dyadicUnary readbackUnary dyadicReadbackSeal
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed sealUnary transportUnary sealTransportEndpoint
  have certCore :
      NameCert
        (fun row : BHist =>
          RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail dyadic
              readback sealRow transport route provenance name bundle pkg ∧
            hsame row endpoint)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro endpoint
        (And.intro carrierWitness (hsame_refl endpoint))
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
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            RegularCauchyModulusWitnessLedgerCarrier source witness window normalizer tail
                dyadic readback sealRow transport route provenance name bundle pkg ∧
              hsame row endpoint)
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont witness window normalizer ∧ Cont normalizer tail dyadic ∧
              Cont dyadic readback sealRow ∧ PkgSig bundle endpoint pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row :=
          unary_transport endpointUnary sourceRow.right.symm
        have endpointSameSeal : hsame endpoint sealRow :=
          by
            cases transportEmpty
            exact cont_deterministic sealTransportEndpoint (cont_right_unit sealRow)
        exact
          And.intro (hsame_trans sourceRow.right endpointSameSeal) rowUnary
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨witnessWindowNormalizer, normalizerTailDyadic, dyadicReadbackSeal, endpointPkg⟩
    }
  exact And.intro semantic endpointUnary

end BEDC.Derived.RegularCauchyModulusWitnessLedgerUp
