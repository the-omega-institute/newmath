import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CyclotomicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CyclotomicRootCarrier [AskSetup] [PackageSetup]
    (numField exponent polynomial splittingField primitiveRoot acceptance comparison provenance
      ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory numField ∧ UnaryHistory exponent ∧ UnaryHistory polynomial ∧
    UnaryHistory splittingField ∧ UnaryHistory primitiveRoot ∧
      Cont numField splittingField provenance ∧ Cont exponent polynomial acceptance ∧
        Cont acceptance primitiveRoot ledger ∧ hsame comparison (append provenance acceptance) ∧
          PkgSig bundle ledger pkg

theorem CyclotomicRootCarrier_source_triad_obligation [AskSetup] [PackageSetup]
    {numField exponent polynomial splittingField primitiveRoot acceptance comparison provenance
      ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CyclotomicRootCarrier numField exponent polynomial splittingField primitiveRoot acceptance
        comparison provenance ledger bundle pkg ->
      UnaryHistory numField ∧ UnaryHistory splittingField ∧ UnaryHistory primitiveRoot ∧
        UnaryHistory provenance ∧ UnaryHistory acceptance ∧ UnaryHistory ledger ∧
          hsame provenance (append numField splittingField) ∧
            hsame acceptance (append exponent polynomial) ∧
              hsame ledger (append acceptance primitiveRoot) ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have numFieldUnary : UnaryHistory numField := carrier.left
  have exponentUnary : UnaryHistory exponent := carrier.right.left
  have polynomialUnary : UnaryHistory polynomial := carrier.right.right.left
  have splittingFieldUnary : UnaryHistory splittingField := carrier.right.right.right.left
  have primitiveRootUnary : UnaryHistory primitiveRoot := carrier.right.right.right.right.left
  have provenanceCont : Cont numField splittingField provenance :=
    carrier.right.right.right.right.right.left
  have acceptanceCont : Cont exponent polynomial acceptance :=
    carrier.right.right.right.right.right.right.left
  have ledgerCont : Cont acceptance primitiveRoot ledger :=
    carrier.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed numFieldUnary splittingFieldUnary provenanceCont
  have acceptanceUnary : UnaryHistory acceptance :=
    unary_cont_closed exponentUnary polynomialUnary acceptanceCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed acceptanceUnary primitiveRootUnary ledgerCont
  exact And.intro numFieldUnary
    (And.intro splittingFieldUnary
      (And.intro primitiveRootUnary
        (And.intro provenanceUnary
          (And.intro acceptanceUnary
            (And.intro ledgerUnary
              (And.intro provenanceCont
                (And.intro acceptanceCont
                  (And.intro ledgerCont
                    carrier.right.right.right.right.right.right.right.right.right))))))))

theorem CyclotomicRootCarrier_root_layer_classifier_transport [AskSetup] [PackageSetup]
    {numField exponent polynomial splittingField primitiveRoot acceptance comparison provenance
      ledger numField' exponent' polynomial' splittingField' primitiveRoot' acceptance'
      provenance' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CyclotomicRootCarrier numField exponent polynomial splittingField primitiveRoot acceptance
        comparison provenance ledger bundle pkg ->
      hsame numField numField' ->
        hsame exponent exponent' ->
          hsame polynomial polynomial' ->
            hsame splittingField splittingField' ->
              hsame primitiveRoot primitiveRoot' ->
                Cont numField' splittingField' provenance' ->
                  Cont exponent' polynomial' acceptance' ->
                    Cont acceptance' primitiveRoot' ledger' ->
                      PkgSig bundle ledger' pkg ->
                        CyclotomicRootCarrier numField' exponent' polynomial' splittingField'
                            primitiveRoot' acceptance' comparison provenance' ledger' bundle pkg ∧
                          hsame provenance provenance' ∧ hsame acceptance acceptance' ∧
                            hsame ledger ledger' := by
  intro carrier sameNumField sameExponent samePolynomial sameSplittingField samePrimitiveRoot
    provenanceCont' acceptanceCont' ledgerCont' pkgSig'
  have numFieldUnary' : UnaryHistory numField' :=
    unary_transport carrier.left sameNumField
  have exponentUnary' : UnaryHistory exponent' :=
    unary_transport carrier.right.left sameExponent
  have polynomialUnary' : UnaryHistory polynomial' :=
    unary_transport carrier.right.right.left samePolynomial
  have splittingFieldUnary' : UnaryHistory splittingField' :=
    unary_transport carrier.right.right.right.left sameSplittingField
  have primitiveRootUnary' : UnaryHistory primitiveRoot' :=
    unary_transport carrier.right.right.right.right.left samePrimitiveRoot
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameNumField sameSplittingField
      carrier.right.right.right.right.right.left provenanceCont'
  have sameAcceptance : hsame acceptance acceptance' :=
    cont_respects_hsame sameExponent samePolynomial
      carrier.right.right.right.right.right.right.left acceptanceCont'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameAcceptance samePrimitiveRoot
      carrier.right.right.right.right.right.right.right.left ledgerCont'
  have sameComparison' :
      hsame comparison (append provenance' acceptance') := by
    cases sameProvenance
    cases sameAcceptance
    exact carrier.right.right.right.right.right.right.right.right.left
  have carrier' :
      CyclotomicRootCarrier numField' exponent' polynomial' splittingField' primitiveRoot'
        acceptance' comparison provenance' ledger' bundle pkg :=
    And.intro numFieldUnary'
      (And.intro exponentUnary'
        (And.intro polynomialUnary'
          (And.intro splittingFieldUnary'
            (And.intro primitiveRootUnary'
              (And.intro provenanceCont'
                (And.intro acceptanceCont'
                  (And.intro ledgerCont'
                    (And.intro sameComparison' pkgSig'))))))))
  exact And.intro carrier' (And.intro sameProvenance (And.intro sameAcceptance sameLedger))

def CyclotomicRootClassifier [AskSetup] [PackageSetup]
    (numField0 exponent0 polynomial0 splittingField0 primitiveRoot0 acceptance0 comparison0
      provenance0 ledger0 numField1 exponent1 polynomial1 splittingField1 primitiveRoot1
      acceptance1 comparison1 provenance1 ledger1 : BHist)
    (bundle0 bundle1 : ProbeBundle ProbeName) (pkg0 pkg1 : Pkg) : Prop :=
  CyclotomicRootCarrier numField0 exponent0 polynomial0 splittingField0 primitiveRoot0
      acceptance0 comparison0 provenance0 ledger0 bundle0 pkg0 ∧
    CyclotomicRootCarrier numField1 exponent1 polynomial1 splittingField1 primitiveRoot1
      acceptance1 comparison1 provenance1 ledger1 bundle1 pkg1 ∧
      hsame numField0 numField1 ∧ hsame exponent0 exponent1 ∧
        hsame polynomial0 polynomial1 ∧ hsame splittingField0 splittingField1 ∧
          hsame primitiveRoot0 primitiveRoot1

theorem CyclotomicRootClassifier_trans [AskSetup] [PackageSetup]
    {numField0 exponent0 polynomial0 splittingField0 primitiveRoot0 acceptance0 comparison0
      provenance0 ledger0 numField1 exponent1 polynomial1 splittingField1 primitiveRoot1
      acceptance1 comparison1 provenance1 ledger1 numField2 exponent2 polynomial2 splittingField2
      primitiveRoot2 acceptance2 comparison2 provenance2 ledger2 : BHist}
    {bundle0 bundle1 bundle2 : ProbeBundle ProbeName} {pkg0 pkg1 pkg2 : Pkg} :
    CyclotomicRootClassifier numField0 exponent0 polynomial0 splittingField0 primitiveRoot0
        acceptance0 comparison0 provenance0 ledger0 numField1 exponent1 polynomial1
        splittingField1 primitiveRoot1 acceptance1 comparison1 provenance1 ledger1 bundle0 bundle1
        pkg0 pkg1 ->
      CyclotomicRootClassifier numField1 exponent1 polynomial1 splittingField1 primitiveRoot1
          acceptance1 comparison1 provenance1 ledger1 numField2 exponent2 polynomial2
          splittingField2 primitiveRoot2 acceptance2 comparison2 provenance2 ledger2 bundle1
          bundle2 pkg1 pkg2 ->
        CyclotomicRootClassifier numField0 exponent0 polynomial0 splittingField0 primitiveRoot0
          acceptance0 comparison0 provenance0 ledger0 numField2 exponent2 polynomial2
          splittingField2 primitiveRoot2 acceptance2 comparison2 provenance2 ledger2 bundle0 bundle2
          pkg0 pkg2 := by
  intro classified01 classified12
  constructor
  · exact classified01.left
  · constructor
    · exact classified12.right.left
    · constructor
      · exact hsame_trans classified01.right.right.left classified12.right.right.left
      · constructor
        · exact hsame_trans classified01.right.right.right.left classified12.right.right.right.left
        · constructor
          · exact hsame_trans classified01.right.right.right.right.left
              classified12.right.right.right.right.left
          · constructor
            · exact hsame_trans classified01.right.right.right.right.right.left
                classified12.right.right.right.right.right.left
            · exact hsame_trans classified01.right.right.right.right.right.right
                classified12.right.right.right.right.right.right

end BEDC.Derived.CyclotomicUp
