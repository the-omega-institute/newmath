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

theorem CyclotomicRootCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {numField exponent polynomial splittingField primitiveRoot acceptance comparison provenance
      ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CyclotomicRootCarrier numField exponent polynomial splittingField primitiveRoot acceptance
        comparison provenance ledger bundle pkg ->
      UnaryHistory numField ∧ UnaryHistory exponent ∧ UnaryHistory polynomial ∧
        UnaryHistory splittingField ∧ UnaryHistory primitiveRoot ∧ UnaryHistory acceptance ∧
          UnaryHistory provenance ∧ UnaryHistory ledger ∧
            Cont numField splittingField provenance ∧ Cont exponent polynomial acceptance ∧
              Cont acceptance primitiveRoot ledger ∧ hsame comparison (append provenance acceptance) ∧
                PkgSig bundle ledger pkg := by
  intro carrier
  have sourceRows :=
    CyclotomicRootCarrier_source_triad_obligation (bundle := bundle) (pkg := pkg) carrier
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
            (And.intro sourceRows.right.right.right.right.left
              (And.intro sourceRows.right.right.right.left
                (And.intro sourceRows.right.right.right.right.right.left
                  (And.intro carrier.right.right.right.right.right.left
                    (And.intro carrier.right.right.right.right.right.right.left
                      (And.intro carrier.right.right.right.right.right.right.right.left
                        (And.intro carrier.right.right.right.right.right.right.right.right.left
                          sourceRows.right.right.right.right.right.right.right.right.right)))))))))))

theorem CyclotomicRootCarrier_root_action_pkg_provenance [AskSetup] [PackageSetup]
    {numField exponent polynomial splittingField primitiveRoot acceptance comparison provenance
      ledger action : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CyclotomicRootCarrier numField exponent polynomial splittingField primitiveRoot acceptance
        comparison provenance ledger bundle pkg ->
      Cont ledger provenance action ->
        UnaryHistory action ∧ PkgSig bundle ledger pkg ∧
          hsame comparison (append provenance acceptance) := by
  intro carrier actionCont
  have sourceRows :=
    CyclotomicRootCarrier_source_triad_obligation (bundle := bundle) (pkg := pkg) carrier
  have provenanceUnary : UnaryHistory provenance :=
    sourceRows.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    sourceRows.right.right.right.right.right.left
  have actionUnary : UnaryHistory action :=
    unary_cont_closed ledgerUnary provenanceUnary actionCont
  exact And.intro actionUnary
    (And.intro sourceRows.right.right.right.right.right.right.right.right.right
      carrier.right.right.right.right.right.right.right.right.left)

theorem CyclotomicRootCarrier_polynomial_ledger_exactness [AskSetup] [PackageSetup]
    {numField exponent polynomial splittingField primitiveRoot acceptance comparison provenance
      ledger factorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CyclotomicRootCarrier numField exponent polynomial splittingField primitiveRoot acceptance
        comparison provenance ledger bundle pkg ->
      Cont splittingField ledger factorRead ->
        UnaryHistory polynomial ∧ UnaryHistory acceptance ∧ UnaryHistory ledger ∧
          UnaryHistory factorRead ∧ hsame acceptance (append exponent polynomial) ∧
            hsame ledger (append acceptance primitiveRoot) ∧
              hsame factorRead (append splittingField ledger) ∧
                hsame comparison (append provenance acceptance) ∧ PkgSig bundle ledger pkg := by
  intro carrier factorReadCont
  have sourceRows :=
    CyclotomicRootCarrier_source_triad_obligation (bundle := bundle) (pkg := pkg) carrier
  have factorReadUnary : UnaryHistory factorRead :=
    unary_cont_closed sourceRows.right.left sourceRows.right.right.right.right.right.left
      factorReadCont
  exact And.intro carrier.right.right.left
    (And.intro sourceRows.right.right.right.right.left
      (And.intro sourceRows.right.right.right.right.right.left
        (And.intro factorReadUnary
          (And.intro sourceRows.right.right.right.right.right.right.right.left
            (And.intro sourceRows.right.right.right.right.right.right.right.right.left
              (And.intro factorReadCont
                (And.intro carrier.right.right.right.right.right.right.right.right.left
                  sourceRows.right.right.right.right.right.right.right.right.right)))))))

theorem CyclotomicRootCarrier_consumer_boundary [AskSetup] [PackageSetup]
    {numField exponent polynomial splittingField primitiveRoot acceptance comparison provenance
      ledger consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CyclotomicRootCarrier numField exponent polynomial splittingField primitiveRoot acceptance
        comparison provenance ledger bundle pkg ->
      Cont ledger comparison consumer ->
        UnaryHistory consumer ∧ hsame consumer (append ledger comparison) ∧
          hsame provenance (append numField splittingField) ∧
            hsame acceptance (append exponent polynomial) ∧
              hsame ledger (append acceptance primitiveRoot) ∧ PkgSig bundle ledger pkg := by
  intro carrier consumerRow
  have sourceRows :=
    CyclotomicRootCarrier_source_triad_obligation (bundle := bundle) (pkg := pkg) carrier
  have comparisonAppendUnary : UnaryHistory (append provenance acceptance) :=
    unary_append_closed sourceRows.right.right.right.left sourceRows.right.right.right.right.left
  have comparisonUnary : UnaryHistory comparison :=
    unary_transport_symm comparisonAppendUnary carrier.right.right.right.right.right.right.right.right.left
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed sourceRows.right.right.right.right.right.left comparisonUnary consumerRow
  exact And.intro consumerUnary
    (And.intro consumerRow
      (And.intro sourceRows.right.right.right.right.right.right.left
        (And.intro sourceRows.right.right.right.right.right.right.right.left
          (And.intro sourceRows.right.right.right.right.right.right.right.right.left
            sourceRows.right.right.right.right.right.right.right.right.right))))

theorem CyclotomicRootCarrier_iwasawa_source_boundary [AskSetup] [PackageSetup]
    {numField exponent polynomial splittingField primitiveRoot acceptance comparison provenance
      ledger consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CyclotomicRootCarrier numField exponent polynomial splittingField primitiveRoot acceptance
        comparison provenance ledger bundle pkg ->
      Cont ledger comparison consumer ->
        UnaryHistory numField ∧ UnaryHistory exponent ∧ UnaryHistory primitiveRoot ∧
          UnaryHistory consumer ∧ hsame acceptance (append exponent polynomial) ∧
            hsame ledger (append acceptance primitiveRoot) ∧ PkgSig bundle ledger pkg := by
  intro carrier consumerRow
  have sourceRows :=
    CyclotomicRootCarrier_source_triad_obligation (bundle := bundle) (pkg := pkg) carrier
  have consumerBoundary :=
    CyclotomicRootCarrier_consumer_boundary (bundle := bundle) (pkg := pkg) carrier consumerRow
  exact And.intro sourceRows.left
    (And.intro carrier.right.left
      (And.intro sourceRows.right.right.left
        (And.intro consumerBoundary.left
          (And.intro sourceRows.right.right.right.right.right.right.right.left
            (And.intro sourceRows.right.right.right.right.right.right.right.right.left
              sourceRows.right.right.right.right.right.right.right.right.right)))))

theorem CyclotomicRootCarrier_positive_exponent_row_coverage [AskSetup] [PackageSetup]
    {numField exponent polynomial splittingField primitiveRoot acceptance comparison provenance
      ledger exponentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CyclotomicRootCarrier numField exponent polynomial splittingField primitiveRoot acceptance
        comparison provenance ledger bundle pkg →
      Cont exponent ledger exponentRead →
        UnaryHistory exponent ∧ hsame acceptance (append exponent polynomial) ∧
          hsame ledger (append acceptance primitiveRoot) ∧
            hsame exponentRead (append exponent ledger) ∧ PkgSig bundle ledger pkg := by
  intro carrier exponentReadCont
  exact And.intro carrier.right.left
    (And.intro carrier.right.right.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.right.right.left
        (And.intro exponentReadCont
          carrier.right.right.right.right.right.right.right.right.right)))

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

theorem CyclotomicRootClassifier_symm [AskSetup] [PackageSetup]
    {numField0 exponent0 polynomial0 splittingField0 primitiveRoot0 acceptance0 comparison0
      provenance0 ledger0 numField1 exponent1 polynomial1 splittingField1 primitiveRoot1
      acceptance1 comparison1 provenance1 ledger1 : BHist}
    {bundle0 bundle1 : ProbeBundle ProbeName} {pkg0 pkg1 : Pkg} :
    CyclotomicRootClassifier numField0 exponent0 polynomial0 splittingField0 primitiveRoot0
        acceptance0 comparison0 provenance0 ledger0 numField1 exponent1 polynomial1
        splittingField1 primitiveRoot1 acceptance1 comparison1 provenance1 ledger1 bundle0 bundle1
        pkg0 pkg1 ->
      CyclotomicRootClassifier numField1 exponent1 polynomial1 splittingField1 primitiveRoot1
        acceptance1 comparison1 provenance1 ledger1 numField0 exponent0 polynomial0
        splittingField0 primitiveRoot0 acceptance0 comparison0 provenance0 ledger0 bundle1
        bundle0 pkg1 pkg0 := by
  intro classified
  constructor
  · exact classified.right.left
  · constructor
    · exact classified.left
    · constructor
      · exact hsame_symm classified.right.right.left
      · constructor
        · exact hsame_symm classified.right.right.right.left
        · constructor
          · exact hsame_symm classified.right.right.right.right.left
          · constructor
            · exact hsame_symm classified.right.right.right.right.right.left
            · exact hsame_symm classified.right.right.right.right.right.right

theorem CyclotomicRootClassifier_downstream_consumer_transport [AskSetup] [PackageSetup]
    {numField0 exponent0 polynomial0 splittingField0 primitiveRoot0 acceptance0 comparison0
      provenance0 ledger0 numField1 exponent1 polynomial1 splittingField1 primitiveRoot1
      acceptance1 comparison1 provenance1 ledger1 action0 action1 : BHist}
    {bundle0 bundle1 : ProbeBundle ProbeName} {pkg0 pkg1 : Pkg} :
    CyclotomicRootClassifier numField0 exponent0 polynomial0 splittingField0 primitiveRoot0
        acceptance0 comparison0 provenance0 ledger0 numField1 exponent1 polynomial1
        splittingField1 primitiveRoot1 acceptance1 comparison1 provenance1 ledger1 bundle0 bundle1
        pkg0 pkg1 ->
      Cont ledger0 provenance0 action0 ->
        Cont ledger1 provenance1 action1 ->
          UnaryHistory action0 ∧ UnaryHistory action1 ∧ hsame action0 action1 ∧
            PkgSig bundle0 ledger0 pkg0 ∧ PkgSig bundle1 ledger1 pkg1 := by
  intro classified actionCont0 actionCont1
  have sourceRows0 :=
    CyclotomicRootCarrier_source_triad_obligation (bundle := bundle0) (pkg := pkg0)
      classified.left
  have sourceRows1 :=
    CyclotomicRootCarrier_source_triad_obligation (bundle := bundle1) (pkg := pkg1)
      classified.right.left
  have sameProvenance : hsame provenance0 provenance1 :=
    cont_respects_hsame classified.right.right.left
      classified.right.right.right.right.right.left
      classified.left.right.right.right.right.right.left
      classified.right.left.right.right.right.right.right.left
  have sameAcceptance : hsame acceptance0 acceptance1 :=
    cont_respects_hsame classified.right.right.right.left
      classified.right.right.right.right.left
      classified.left.right.right.right.right.right.right.left
      classified.right.left.right.right.right.right.right.right.left
  have sameLedger : hsame ledger0 ledger1 :=
    cont_respects_hsame sameAcceptance classified.right.right.right.right.right.right
      classified.left.right.right.right.right.right.right.right.left
      classified.right.left.right.right.right.right.right.right.right.left
  have action0Unary : UnaryHistory action0 :=
    unary_cont_closed sourceRows0.right.right.right.right.right.left
      sourceRows0.right.right.right.left actionCont0
  have action1Unary : UnaryHistory action1 :=
    unary_cont_closed sourceRows1.right.right.right.right.right.left
      sourceRows1.right.right.right.left actionCont1
  have sameAction : hsame action0 action1 :=
    cont_respects_hsame sameLedger sameProvenance actionCont0 actionCont1
  exact And.intro action0Unary
    (And.intro action1Unary
      (And.intro sameAction
        (And.intro sourceRows0.right.right.right.right.right.right.right.right.right
          sourceRows1.right.right.right.right.right.right.right.right.right)))

theorem CyclotomicRootClassifier_readback_threshold [AskSetup] [PackageSetup]
    {numField0 exponent0 polynomial0 splittingField0 primitiveRoot0 acceptance0 comparison0
      provenance0 ledger0 numField1 exponent1 polynomial1 splittingField1 primitiveRoot1
      acceptance1 comparison1 provenance1 ledger1 read0 read1 : BHist}
    {bundle0 bundle1 : ProbeBundle ProbeName} {pkg0 pkg1 : Pkg} :
    CyclotomicRootClassifier numField0 exponent0 polynomial0 splittingField0 primitiveRoot0
        acceptance0 comparison0 provenance0 ledger0 numField1 exponent1 polynomial1
        splittingField1 primitiveRoot1 acceptance1 comparison1 provenance1 ledger1 bundle0 bundle1
        pkg0 pkg1 ->
      Cont ledger0 comparison0 read0 ->
        Cont ledger1 comparison1 read1 ->
          UnaryHistory read0 ∧ UnaryHistory read1 ∧ hsame read0 read1 ∧
            hsame read0 (append ledger0 comparison0) ∧
              hsame read1 (append ledger1 comparison1) ∧
                PkgSig bundle0 ledger0 pkg0 ∧ PkgSig bundle1 ledger1 pkg1 := by
  intro classified readCont0 readCont1
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
  have sameComparison : hsame comparison0 comparison1 := by
    cases sameProvenance
    cases sameAcceptance
    exact hsame_trans classified.left.right.right.right.right.right.right.right.right.left
      (hsame_symm classified.right.left.right.right.right.right.right.right.right.right.left)
  have comparisonAppendUnary0 : UnaryHistory (append provenance0 acceptance0) :=
    unary_append_closed sourceRows0.right.right.right.left sourceRows0.right.right.right.right.left
  have comparisonUnary0 : UnaryHistory comparison0 :=
    unary_transport_symm comparisonAppendUnary0
      classified.left.right.right.right.right.right.right.right.right.left
  have comparisonAppendUnary1 : UnaryHistory (append provenance1 acceptance1) :=
    unary_append_closed sourceRows1.right.right.right.left sourceRows1.right.right.right.right.left
  have comparisonUnary1 : UnaryHistory comparison1 :=
    unary_transport_symm comparisonAppendUnary1
      classified.right.left.right.right.right.right.right.right.right.right.left
  have readUnary0 : UnaryHistory read0 :=
    unary_cont_closed sourceRows0.right.right.right.right.right.left comparisonUnary0 readCont0
  have readUnary1 : UnaryHistory read1 :=
    unary_cont_closed sourceRows1.right.right.right.right.right.left comparisonUnary1 readCont1
  have sameRead : hsame read0 read1 :=
    cont_respects_hsame sameLedger sameComparison readCont0 readCont1
  exact And.intro readUnary0
    (And.intro readUnary1
      (And.intro sameRead
        (And.intro readCont0
          (And.intro readCont1
            (And.intro sourceRows0.right.right.right.right.right.right.right.right.right
              sourceRows1.right.right.right.right.right.right.right.right.right)))))

end BEDC.Derived.CyclotomicUp
