import BEDC.Derived.FormalConstantEmpiricalValueBoundaryUp.TasteGate

namespace BEDC.Derived.FormalConstantEmpiricalValueBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem FormalConstantEmpiricalValueBoundaryScope
    {formal empirical calibration uncertainty reproducibility failure transport replay provenance
      localCert comparison measurementReplay calibrationReplay : BHist} :
    formalConstantEmpiricalValueBoundaryFields
        (FormalConstantEmpiricalValueBoundaryUp.mk formal empirical calibration uncertainty
          reproducibility failure transport replay provenance localCert) =
      [formal, empirical, calibration, uncertainty, reproducibility, failure, transport, replay,
        provenance, localCert] →
      Cont formal empirical comparison →
        Cont empirical calibration measurementReplay →
          Cont uncertainty reproducibility calibrationReplay →
            UnaryHistory formal →
              UnaryHistory empirical →
                UnaryHistory calibration →
                  UnaryHistory uncertainty →
                    UnaryHistory reproducibility →
                      UnaryHistory comparison ∧ UnaryHistory measurementReplay ∧
                        UnaryHistory calibrationReplay ∧ hsame failure failure ∧
                          hsame localCert localCert := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro hfields formalRoute measurementRoute calibrationRoute formalUnary empiricalUnary
    calibrationUnary uncertaintyUnary reproducibilityUnary
  cases hfields
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed formalUnary empiricalUnary formalRoute
  have measurementReplayUnary : UnaryHistory measurementReplay :=
    unary_cont_closed empiricalUnary calibrationUnary measurementRoute
  have calibrationReplayUnary : UnaryHistory calibrationReplay :=
    unary_cont_closed uncertaintyUnary reproducibilityUnary calibrationRoute
  exact
    ⟨comparisonUnary, measurementReplayUnary, calibrationReplayUnary, hsame_refl failure,
      hsame_refl localCert⟩

end BEDC.Derived.FormalConstantEmpiricalValueBoundaryUp
