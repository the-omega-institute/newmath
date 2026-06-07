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

theorem ParsevalRootRealEnergySealBoundary [AskSetup] [PackageSetup]
    {fourier source pairing integral readback tolerance sealRow transport replay provenance name
      energyRead budgetRead rootSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ParsevalCarrier fourier source pairing integral readback tolerance sealRow transport replay
        provenance name bundle pkg →
      Cont pairing integral energyRead →
        Cont energyRead readback budgetRead →
          Cont budgetRead sealRow rootSeal →
            PkgSig bundle rootSeal pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row rootSeal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
                      hsame row integral ∨ hsame row readback ∨ hsame row tolerance ∨
                        hsame row sealRow ∨ hsame row rootSeal)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont pairing integral energyRead ∧
                      Cont energyRead readback budgetRead ∧
                        Cont budgetRead sealRow rootSeal ∧ PkgSig bundle rootSeal pkg)
                  hsame ∧ UnaryHistory rootSeal := by
  -- BEDC touchpoint anchor: ParsevalCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier pairingIntegralEnergy energyReadbackBudget budgetSealRoot rootPkg
  obtain ⟨fourierUnary, sourceUnary, pairingUnary, integralUnary, readbackUnary,
    toleranceUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _nameUnary, _fourierSourcePairing, _pairingIntegralReadback,
    _readbackToleranceSeal, _sealTransportReplay, _provenancePkg, _namePkg⟩ := carrier
  have energyUnary : UnaryHistory energyRead :=
    unary_cont_closed pairingUnary integralUnary pairingIntegralEnergy
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed energyUnary readbackUnary energyReadbackBudget
  have rootUnary : UnaryHistory rootSeal :=
    unary_cont_closed budgetUnary sealUnary budgetSealRoot
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row fourier ∨ hsame row source ∨ hsame row pairing ∨
              hsame row integral ∨ hsame row readback ∨ hsame row tolerance ∨
                hsame row sealRow ∨ hsame row rootSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont pairing integral energyRead ∧
              Cont energyRead readback budgetRead ∧ Cont budgetRead sealRow rootSeal ∧
                PkgSig bundle rootSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootSeal ⟨hsame_refl rootSeal, rootUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, pairingIntegralEnergy, energyReadbackBudget, budgetSealRoot, rootPkg⟩
  }
  exact ⟨cert, rootUnary⟩

end BEDC.Derived.ParsevalUp
