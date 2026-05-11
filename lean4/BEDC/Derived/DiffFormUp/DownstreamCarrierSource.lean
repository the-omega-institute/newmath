import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DiffFormDownstreamCarrierSource_obligation
    {degree probe tensor antisym source boundary consumer : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> UnaryHistory tensor -> UnaryHistory antisym ->
      Cont degree probe source -> Cont tensor antisym boundary -> Cont source boundary consumer ->
        UnaryHistory source ∧ UnaryHistory boundary ∧ UnaryHistory consumer ∧
          hsame source (append degree probe) ∧ hsame boundary (append tensor antisym) ∧
            hsame consumer (append source boundary) := by
  intro degreeUnary probeUnary tensorUnary antisymUnary degreeProbe tensorAntisym sourceBoundary
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed degreeUnary probeUnary degreeProbe
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed tensorUnary antisymUnary tensorAntisym
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sourceUnary boundaryUnary sourceBoundary
  exact And.intro sourceUnary
    (And.intro boundaryUnary
      (And.intro consumerUnary
        (And.intro degreeProbe
          (And.intro tensorAntisym sourceBoundary))))

end BEDC.Derived.DiffFormUp
