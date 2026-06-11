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

theorem ParsevalSoneBasisLedger [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      basisRead pairingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont source fourier basisRead →
        Cont basisRead pairing pairingRead →
          PkgSig bundle pairingRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row pairingRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row fourier ∨ hsame row pairing ∨
                    hsame row basisRead ∨ hsame row pairingRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont source fourier basisRead ∧
                    Cont basisRead pairing pairingRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle pairingRead pkg)
                hsame ∧
              UnaryHistory basisRead ∧ UnaryHistory pairingRead := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier sourceFourierBasis basisPairingRead pairingReadPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, _integralUnary, _readbackUnary,
    _toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _fourierSourcePairing, _pairingIntegralReadback, _readbackToleranceSeal,
    _sealTransportReplay, provenancePkg, _namePkg⟩ := carrier
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed sourceUnary fourierUnary sourceFourierBasis
  have pairingReadUnary : UnaryHistory pairingRead :=
    unary_cont_closed basisUnary pairingUnary basisPairingRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row pairingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row fourier ∨ hsame row pairing ∨
              hsame row basisRead ∨ hsame row pairingRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source fourier basisRead ∧
              Cont basisRead pairing pairingRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle pairingRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro pairingRead ⟨hsame_refl pairingRead, pairingReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceFourierBasis, basisPairingRead, provenancePkg,
          pairingReadPkg⟩
  }
  exact ⟨cert, basisUnary, pairingReadUnary⟩

end BEDC.Derived.ParsevalUp
