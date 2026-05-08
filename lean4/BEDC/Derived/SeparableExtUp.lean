import BEDC.Derived.FieldExtUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.SeparableExtUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.FieldExtUp
open BEDC.Derived.PolynomialUp

def SeparableExtSourceRow
    (fieldPacket polynomialPacket minimalPolynomial simpleRoot provenance : BHist) : Prop :=
  FieldExtSingletonCarrier fieldPacket ∧
    PolynomialSingletonCarrier polynomialPacket ∧
      PolynomialSingletonClassifier minimalPolynomial BHist.Empty ∧
        Cont minimalPolynomial simpleRoot provenance

theorem SeparableExtFieldPolynomialSource_rows
    {fieldPacket polynomialPacket minimalPolynomial simpleRoot provenance : BHist} :
    FieldExtSingletonCarrier fieldPacket ->
      PolynomialSingletonCarrier polynomialPacket ->
        PolynomialSingletonClassifier minimalPolynomial BHist.Empty ->
          Cont minimalPolynomial simpleRoot provenance ->
            SeparableExtSourceRow fieldPacket polynomialPacket minimalPolynomial simpleRoot
                provenance ∧
              hsame provenance (append minimalPolynomial simpleRoot) := by
  intro fieldCarrier polynomialCarrier minimalPolynomialClassified provenanceCont
  exact And.intro
    (And.intro fieldCarrier
      (And.intro polynomialCarrier
        (And.intro minimalPolynomialClassified provenanceCont)))
    provenanceCont

end BEDC.Derived.SeparableExtUp
