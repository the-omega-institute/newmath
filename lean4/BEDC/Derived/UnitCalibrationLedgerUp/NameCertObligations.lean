import BEDC.Derived.UnitCalibrationLedgerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UnitCalibrationLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UnitCalibrationLedgerCarrier [AskSetup] [PackageSetup]
    (measurement unitBridge calibration uncertainty instrument reproducibility dimension
      classifier transport provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  UnaryHistory measurement ∧ UnaryHistory unitBridge ∧ UnaryHistory calibration ∧
    UnaryHistory uncertainty ∧ UnaryHistory instrument ∧ UnaryHistory reproducibility ∧
      UnaryHistory dimension ∧ UnaryHistory classifier ∧ UnaryHistory transport ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont measurement unitBridge classifier ∧ hsame transport transport ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem UnitCalibrationLedgerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {measurement unitBridge calibration uncertainty instrument reproducibility dimension
      classifier transport provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnitCalibrationLedgerCarrier measurement unitBridge calibration uncertainty instrument
        reproducibility dimension classifier transport provenance name bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row measurement ∨ hsame row unitBridge ∨ hsame row calibration ∨
              hsame row uncertainty ∨ hsame row instrument ∨ hsame row reproducibility ∨
                hsame row dimension ∨ Cont measurement unitBridge classifier)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧ hsame row name)
          hsame ∧
        UnaryHistory measurement ∧ UnaryHistory unitBridge ∧ UnaryHistory calibration ∧
          UnaryHistory uncertainty ∧ UnaryHistory instrument ∧ UnaryHistory reproducibility ∧
            UnaryHistory dimension ∧ UnaryHistory classifier ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨measurementUnary, unitBridgeUnary, calibrationUnary, uncertaintyUnary,
    instrumentUnary, reproducibilityUnary, dimensionUnary, classifierUnary, _transportUnary,
    _provenanceUnary, nameUnary, measurementUnitClassifier, _transportSelf,
    provenancePkg, namePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row name ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row measurement ∨ hsame row unitBridge ∨ hsame row calibration ∨
              hsame row uncertainty ∨ hsame row instrument ∨ hsame row reproducibility ∨
                hsame row dimension ∨ Cont measurement unitBridge classifier)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧ hsame row name)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro name ⟨hsame_refl name, nameUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        measurementUnitClassifier))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, namePkg, source.left⟩
  }
  exact
    ⟨cert, measurementUnary, unitBridgeUnary, calibrationUnary, uncertaintyUnary,
      instrumentUnary, reproducibilityUnary, dimensionUnary, classifierUnary,
      provenancePkg, namePkg⟩

end BEDC.Derived.UnitCalibrationLedgerUp
