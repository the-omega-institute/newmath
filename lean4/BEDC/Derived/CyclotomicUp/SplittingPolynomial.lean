import BEDC.Derived.CyclotomicUp

namespace BEDC.Derived.CyclotomicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CyclotomicRootCarrier_splitting_polynomial_classifier_transport [AskSetup]
    [PackageSetup]
    {numField0 exponent0 polynomial0 splittingField0 primitiveRoot0 acceptance0 comparison0
      provenance0 ledger0 numField1 exponent1 polynomial1 splittingField1 primitiveRoot1
      acceptance1 comparison1 provenance1 ledger1 factorRead0 factorRead1 : BHist}
    {bundle0 bundle1 : ProbeBundle ProbeName} {pkg0 pkg1 : Pkg} :
    CyclotomicRootClassifier numField0 exponent0 polynomial0 splittingField0 primitiveRoot0
        acceptance0 comparison0 provenance0 ledger0 numField1 exponent1 polynomial1
        splittingField1 primitiveRoot1 acceptance1 comparison1 provenance1 ledger1 bundle0 bundle1
        pkg0 pkg1 ->
      Cont splittingField0 ledger0 factorRead0 ->
        Cont splittingField1 ledger1 factorRead1 ->
          UnaryHistory polynomial0 ∧ UnaryHistory polynomial1 ∧ UnaryHistory factorRead0 ∧
            UnaryHistory factorRead1 ∧ hsame polynomial0 polynomial1 ∧
              hsame factorRead0 factorRead1 ∧ hsame primitiveRoot0 primitiveRoot1 ∧
                PkgSig bundle0 ledger0 pkg0 ∧ PkgSig bundle1 ledger1 pkg1 := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro classified factorReadCont0 factorReadCont1
  have sourceRows0 :=
    CyclotomicRootCarrier_source_triad_obligation (bundle := bundle0) (pkg := pkg0)
      classified.left
  have sourceRows1 :=
    CyclotomicRootCarrier_source_triad_obligation (bundle := bundle1) (pkg := pkg1)
      classified.right.left
  have sameProvenance : hsame provenance0 provenance1 :=
    cont_respects_hsame classified.right.right.left classified.right.right.right.right.right.left
      classified.left.right.right.right.right.right.left
      classified.right.left.right.right.right.right.right.left
  have sameAcceptance : hsame acceptance0 acceptance1 :=
    cont_respects_hsame classified.right.right.right.left classified.right.right.right.right.left
      classified.left.right.right.right.right.right.right.left
      classified.right.left.right.right.right.right.right.right.left
  have sameLedger : hsame ledger0 ledger1 :=
    cont_respects_hsame sameAcceptance classified.right.right.right.right.right.right
      classified.left.right.right.right.right.right.right.right.left
      classified.right.left.right.right.right.right.right.right.right.left
  have factorReadUnary0 : UnaryHistory factorRead0 :=
    unary_cont_closed sourceRows0.right.left sourceRows0.right.right.right.right.right.left
      factorReadCont0
  have factorReadUnary1 : UnaryHistory factorRead1 :=
    unary_cont_closed sourceRows1.right.left sourceRows1.right.right.right.right.right.left
      factorReadCont1
  have sameFactorRead : hsame factorRead0 factorRead1 :=
    cont_respects_hsame classified.right.right.right.right.right.left sameLedger
      factorReadCont0 factorReadCont1
  exact
    ⟨classified.left.right.right.left, classified.right.left.right.right.left,
      factorReadUnary0, factorReadUnary1, classified.right.right.right.right.left,
      sameFactorRead, classified.right.right.right.right.right.right,
      sourceRows0.right.right.right.right.right.right.right.right.right,
      sourceRows1.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.CyclotomicUp
