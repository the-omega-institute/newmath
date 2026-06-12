import BEDC.Derived.ParsevalUp.RootEnergyCarrierAdmission
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ParsevalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ParsevalSoneOrthogonalityHandoff [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont source pairing handoff →
        Cont handoff integral sealRow →
          SemanticNameCert
              (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row pairing ∨ hsame row integral ∨
                  hsame row readback ∨ hsame row tolerance ∨ hsame row sealRow ∨
                    hsame row handoff)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont source pairing handoff ∧
                  Cont handoff integral sealRow ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle name pkg)
              hsame ∧
            UnaryHistory handoff := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourcePairingHandoff handoffIntegralSeal
  obtain ⟨_fourierUnary, sourceUnary, pairingUnary, integralUnary, _readbackUnary,
    _toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _fourierSourcePairing, _pairingIntegralReadback, _readbackToleranceSeal,
    _sealTransportReplay, provenancePkg, namePkg⟩ := carrier
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed sourceUnary pairingUnary sourcePairingHandoff
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro handoff ⟨hsame_refl handoff, handoffUnary⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
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
          ⟨source.right, sourcePairingHandoff, handoffIntegralSeal,
            provenancePkg, namePkg⟩
    }
  · exact handoffUnary

end BEDC.Derived.ParsevalUp
