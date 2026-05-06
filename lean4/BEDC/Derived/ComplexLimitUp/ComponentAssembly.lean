import BEDC.Derived.ComplexLimitUp

namespace BEDC.Derived.ComplexLimitUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.ComplexUp

theorem ComplexLimit_component_assembly_candidate_unary {real imag z Mx My Msharp : BHist} :
    BEDC.Derived.RatUp.RatHistoryCarrier real ->
      BEDC.Derived.RatUp.RatHistoryCarrier imag ->
        Cont real imag z ->
          UnaryHistory Mx ->
            UnaryHistory My ->
              Cont Mx My Msharp -> ComplexHistoryCarrier z ∧ UnaryHistory Msharp := by
  intro realCarrier imagCarrier componentAssembly modulusX modulusY modulusAssembly
  have candidateCarrier : ComplexHistoryCarrier z :=
    Exists.intro real
      (Exists.intro imag
        (And.intro realCarrier (And.intro imagCarrier componentAssembly)))
  exact And.intro candidateCarrier (unary_cont_closed modulusX modulusY modulusAssembly)

end BEDC.Derived.ComplexLimitUp
