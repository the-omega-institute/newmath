import BEDC.Derived.CauchyModulusUp

namespace BEDC.Derived.CauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusUp_StdBridge [AskSetup] [PackageSetup]
    {precision threshold tolerance schedule window consumption provenance publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusCarrierPacket precision threshold tolerance schedule window consumption
        provenance →
      Cont precision threshold window →
        Cont window tolerance consumption →
          Cont consumption schedule publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row precision ∨ hsame row threshold ∨ hsame row tolerance ∨
                      hsame row schedule ∨ hsame row window ∨ hsame row consumption ∨
                        hsame row provenance ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont precision threshold window ∧
                      Cont window tolerance consumption ∧ Cont consumption schedule publicRead ∧
                        PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet precisionThresholdWindow windowToleranceConsumption consumptionScheduleRead
    readPkg
  obtain ⟨_precisionUnary, _thresholdUnary, _tolerancePositive, scheduleUnary,
    _windowUnary, consumptionUnary, _provenanceUnary, _precisionToleranceThreshold,
    _thresholdScheduleConsumption, _consumptionProvenanceWindow⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed consumptionUnary scheduleUnary consumptionScheduleRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row precision ∨ hsame row threshold ∨ hsame row tolerance ∨
              hsame row schedule ∨ hsame row window ∨ hsame row consumption ∨
                hsame row provenance ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont precision threshold window ∧
              Cont window tolerance consumption ∧ Cont consumption schedule publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, precisionThresholdWindow, windowToleranceConsumption,
          consumptionScheduleRead, readPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.CauchyModulusUp
