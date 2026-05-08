import BEDC.Derived.FieldExtUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SeparableExtUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.FieldExtUp
open BEDC.Derived.PolynomialUp

def SeparableExtJointSource
    (field polynomial generator minpoly derivative provenance endpoint : BHist) : Prop :=
  FieldExtSingletonCarrier field ∧ PolynomialSingletonCarrier polynomial ∧
    UnaryHistory generator ∧ UnaryHistory derivative ∧
      PolynomialSingletonClassifier minpoly polynomial ∧ Cont polynomial derivative provenance ∧
        Cont provenance generator endpoint

theorem SeparableExtJointSource_fieldext_polynomial_source
    {field polynomial generator minpoly derivative provenance endpoint : BHist} :
    SeparableExtJointSource field polynomial generator minpoly derivative provenance endpoint ->
      FieldExtSingletonCarrier field ∧ PolynomialSingletonCarrier polynomial ∧
        UnaryHistory generator ∧ UnaryHistory derivative ∧
          PolynomialSingletonClassifier minpoly polynomial ∧
            Cont polynomial derivative provenance ∧ Cont provenance generator endpoint ∧
              UnaryHistory endpoint ∧
                hsame endpoint (append (append polynomial derivative) generator) := by
  intro source
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed
      (unary_transport unary_empty (hsame_symm source.right.left))
      source.right.right.right.left
      source.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary source.right.right.left
      source.right.right.right.right.right.right
  have endpointReadback :
      hsame endpoint (append (append polynomial derivative) generator) :=
    hsame_trans source.right.right.right.right.right.right
      (congrArg (fun row : BHist => append row generator)
        source.right.right.right.right.right.left)
  exact And.intro source.left
    (And.intro source.right.left
      (And.intro source.right.right.left
        (And.intro source.right.right.right.left
          (And.intro source.right.right.right.right.left
            (And.intro source.right.right.right.right.right.left
              (And.intro source.right.right.right.right.right.right
                (And.intro endpointUnary endpointReadback)))))))

end BEDC.Derived.SeparableExtUp
