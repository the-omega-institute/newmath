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

theorem ComplexLimit_component_limits_closed {s N M : BHist -> BHist}
    {real imag z : BHist} :
    ComplexRegularSequence s N -> BEDC.Derived.RatUp.RatHistoryCarrier real ->
      BEDC.Derived.RatUp.RatHistoryCarrier imag -> Cont real imag z ->
        (forall {k n : BHist}, UnaryHistory k -> UnaryHistory n -> Cont (M k) n n ->
          exists d : BHist, ComplexDistance (s n) z d) ->
            ComplexLimit s N z M := by
  intro regular realCarrier imagCarrier componentAssembly modulus
  have candidateCarrier : ComplexHistoryCarrier z :=
    Exists.intro real
      (Exists.intro imag
        (And.intro realCarrier (And.intro imagCarrier componentAssembly)))
  exact And.intro regular
    (And.intro candidateCarrier
      (fun k n unaryK unaryN controlled => modulus unaryK unaryN controlled))

theorem ComplexLimit_from_component_limits {s N : BHist -> BHist}
    {real imag Mx My Mstar : BHist} :
    (forall {n : BHist}, UnaryHistory n -> ComplexHistoryCarrier (s n)) ->
      ComplexRegularSequence s N ->
        BEDC.Derived.RatUp.RatHistoryCarrier real ->
          BEDC.Derived.RatUp.RatHistoryCarrier imag ->
            UnaryHistory Mx ->
              UnaryHistory My ->
                Cont Mx My Mstar ->
                  exists z : BHist,
                    ComplexHistoryCarrier z ∧ UnaryHistory Mstar ∧
                      ComplexLimit s N z (fun _ : BHist => Mstar) := by
  intro sequenceCarrier regular realCarrier imagCarrier modulusX modulusY modulusAssembly
  let z := append real imag
  have zAssembly : Cont real imag z := cont_intro rfl
  have assembled := ComplexLimit_component_assembly_candidate_unary realCarrier imagCarrier
    zAssembly modulusX modulusY modulusAssembly
  have limitModulus :
      forall k n : BHist, UnaryHistory k -> UnaryHistory n -> Cont ((fun _ : BHist => Mstar) k) n n ->
        exists d : BHist, ComplexDistance (s n) z d := by
    intro _k n _unaryK unaryN _controlled
    exact Exists.intro (append (s n) z)
      (And.intro (ComplexHistoryCarrier_unary (sequenceCarrier unaryN))
        (And.intro (ComplexHistoryCarrier_unary assembled.left)
          (And.intro
            (unary_append_closed
              (ComplexHistoryCarrier_unary (sequenceCarrier unaryN))
              (ComplexHistoryCarrier_unary assembled.left))
            (Or.inl (cont_intro rfl)))))
  exact Exists.intro z
    (And.intro assembled.left
      (And.intro assembled.right
        (And.intro regular (And.intro assembled.left limitModulus))))

end BEDC.Derived.ComplexLimitUp
