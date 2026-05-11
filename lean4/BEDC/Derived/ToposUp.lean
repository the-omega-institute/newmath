import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ToposUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ToposFiniteCarrier [AskSetup] [PackageSetup]
    (category sheaf finiteLimit exponential subobjectClassifier comparison ledger provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory category ∧ UnaryHistory sheaf ∧ UnaryHistory finiteLimit ∧
    UnaryHistory exponential ∧ UnaryHistory subobjectClassifier ∧
      Cont category sheaf comparison ∧ Cont finiteLimit exponential ledger ∧
        Cont ledger subobjectClassifier provenance ∧ Cont comparison provenance endpoint ∧
          PkgSig bundle endpoint pkg

theorem ToposFiniteCarrier_obligation_surface [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobjectClassifier comparison ledger provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier comparison
        ledger provenance endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          hsame ∧
        Cont category sheaf comparison ∧ Cont finiteLimit exponential ledger ∧
          Cont ledger subobjectClassifier provenance ∧ Cont comparison provenance endpoint ∧
            PkgSig bundle endpoint pkg := by
  intro carrierData
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
            comparison ledger provenance e bundle pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro carrierData (hsame_refl endpoint))
  obtain ⟨_categoryUnary, _sheafUnary, _finiteLimitUnary, _exponentialUnary,
    _subobjectClassifierUnary, comparisonRow, ledgerRow, provenanceRow, endpointRow,
    pkgSig⟩ := carrierData
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier
                comparison ledger provenance e bundle pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        cases sourceRow with
        | intro e endpointData =>
            exact Exists.intro e
              (And.intro endpointData.left
                (hsame_trans (hsame_symm sameRows) endpointData.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro comparisonRow
      (And.intro ledgerRow (And.intro provenanceRow (And.intro endpointRow pkgSig))))

def ToposSubobjectClassifierLedger [AskSetup] [PackageSetup]
    (category sheaf finiteLimit exponential subobject contRows provenance endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory category ∧ UnaryHistory sheaf ∧ UnaryHistory finiteLimit ∧
    UnaryHistory exponential ∧ UnaryHistory subobject ∧ UnaryHistory endpoint ∧
      Cont category sheaf finiteLimit ∧ Cont finiteLimit exponential subobject ∧
        Cont subobject contRows endpoint ∧ PkgSig probe provenance pkg

theorem ToposSubobjectClassifierLedger_exactness [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobject contRows provenance endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject contRows
        provenance endpoint probe pkg ->
      UnaryHistory category ∧ UnaryHistory sheaf ∧ UnaryHistory finiteLimit ∧
        UnaryHistory exponential ∧ UnaryHistory subobject ∧ UnaryHistory endpoint ∧
          Cont category sheaf finiteLimit ∧ Cont finiteLimit exponential subobject ∧
            Cont subobject contRows endpoint ∧ PkgSig probe provenance pkg := by
  intro ledger
  have categoryUnary : UnaryHistory category :=
    ledger.left
  have sheafUnary : UnaryHistory sheaf :=
    ledger.right.left
  have finiteLimitUnary : UnaryHistory finiteLimit :=
    unary_cont_closed categoryUnary sheafUnary ledger.right.right.right.right.right.right.left
  have exponentialUnary : UnaryHistory exponential :=
    ledger.right.right.right.left
  have subobjectUnary : UnaryHistory subobject :=
    unary_cont_closed finiteLimitUnary exponentialUnary
      ledger.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    ledger.right.right.right.right.right.left
  have categorySheafRow : Cont category sheaf finiteLimit :=
    ledger.right.right.right.right.right.right.left
  have finiteExponentialRow : Cont finiteLimit exponential subobject :=
    ledger.right.right.right.right.right.right.right.left
  have subobjectEndpointRow : Cont subobject contRows endpoint :=
    ledger.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig probe provenance pkg :=
    ledger.right.right.right.right.right.right.right.right.right
  exact And.intro categoryUnary
    (And.intro sheafUnary
      (And.intro finiteLimitUnary
        (And.intro exponentialUnary
          (And.intro subobjectUnary
            (And.intro endpointUnary
              (And.intro categorySheafRow
                (And.intro finiteExponentialRow (And.intro subobjectEndpointRow pkgSig))))))))

theorem ToposSubobjectClassifier_pullback_boundary [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobject contRows provenance endpoint pullback :
      BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject contRows
        provenance endpoint probe pkg ->
      Cont endpoint subobject pullback ->
        UnaryHistory pullback ∧ Cont category sheaf finiteLimit ∧
          Cont finiteLimit exponential subobject ∧ Cont subobject contRows endpoint ∧
            Cont endpoint subobject pullback ∧ PkgSig probe provenance pkg := by
  intro ledgerRows pullbackRow
  obtain ⟨_categoryUnary, _sheafUnary, _finiteLimitUnary, _exponentialUnary,
    subobjectUnary, endpointUnary, categorySheafRow, finiteExponentialRow,
    subobjectEndpointRow, packageRow⟩ := ToposSubobjectClassifierLedger_exactness ledgerRows
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed endpointUnary subobjectUnary pullbackRow
  exact And.intro pullbackUnary
    (And.intro categorySheafRow
      (And.intro finiteExponentialRow
        (And.intro subobjectEndpointRow (And.intro pullbackRow packageRow))))

theorem ToposFiniteCarrier_site_sheaf_classifier_obligation [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobject comparison ledger provenance endpoint
      classifierEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
        provenance endpoint bundle pkg ->
      ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject ledger
        provenance classifierEndpoint bundle pkg ->
      hsame provenance classifierEndpoint ->
        ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
          classifierEndpoint endpoint bundle pkg ∧
          Cont category sheaf finiteLimit ∧ Cont finiteLimit exponential subobject ∧
            Cont subobject ledger classifierEndpoint := by
  intro carrier ledgerRows sameProvenanceClassifier
  obtain ⟨categoryUnary, sheafUnary, finiteLimitUnary, exponentialUnary, subobjectUnary,
    _endpointUnary, categorySheafRow, finiteExponentialRow, subobjectLedgerRow,
    _packageRow⟩ := ToposSubobjectClassifierLedger_exactness ledgerRows
  obtain ⟨carrierCategoryUnary, carrierSheafUnary, carrierFiniteLimitUnary,
    carrierExponentialUnary, carrierSubobjectUnary, comparisonRow, ledgerRow,
    provenanceRow, endpointRow, packageEndpointRow⟩ := carrier
  have classifierEndpointUnary : UnaryHistory classifierEndpoint :=
    ledgerRows.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed carrierFiniteLimitUnary carrierExponentialUnary ledgerRow
  have ledgerClassifierRow : Cont ledger subobject classifierEndpoint :=
    cont_intro (subobjectLedgerRow.trans (unary_append_comm subobjectUnary ledgerUnary))
  have transportedEndpointRow : Cont comparison classifierEndpoint endpoint :=
    by
      cases sameProvenanceClassifier
      exact endpointRow
  have transportedCarrier :
      ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
          classifierEndpoint endpoint bundle pkg :=
    And.intro carrierCategoryUnary
      (And.intro carrierSheafUnary
        (And.intro carrierFiniteLimitUnary
          (And.intro carrierExponentialUnary
            (And.intro carrierSubobjectUnary
              (And.intro comparisonRow
                (And.intro ledgerRow
                  (And.intro ledgerClassifierRow
                    (And.intro transportedEndpointRow packageEndpointRow))))))))
  exact And.intro transportedCarrier
    (And.intro categorySheafRow (And.intro finiteExponentialRow subobjectLedgerRow))

theorem ToposFiniteCarrier_certificate_boundary [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobject comparison ledger provenance endpoint
      classifierEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
        provenance endpoint bundle pkg ->
      ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject ledger
        provenance classifierEndpoint bundle pkg ->
      hsame provenance classifierEndpoint ->
        SemanticNameCert
            (fun row : BHist =>
              exists e : BHist,
                ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison
                  ledger classifierEndpoint e bundle pkg ∧ hsame row e)
            (fun row : BHist =>
              exists e : BHist,
                ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison
                  ledger classifierEndpoint e bundle pkg ∧ hsame row e)
            (fun row : BHist =>
              exists e : BHist,
                ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison
                  ledger classifierEndpoint e bundle pkg ∧ hsame row e)
            hsame ∧
          ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
            classifierEndpoint endpoint bundle pkg ∧
            Cont category sheaf finiteLimit ∧ Cont finiteLimit exponential subobject ∧
              Cont subobject ledger classifierEndpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier ledgerRows sameProvenanceClassifier
  have transported :
      ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
          classifierEndpoint endpoint bundle pkg ∧
        Cont category sheaf finiteLimit ∧ Cont finiteLimit exponential subobject ∧
          Cont subobject ledger classifierEndpoint :=
    ToposFiniteCarrier_site_sheaf_classifier_obligation carrier ledgerRows
      sameProvenanceClassifier
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
            classifierEndpoint e bundle pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro transported.left (hsame_refl endpoint))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
                classifierEndpoint e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
                classifierEndpoint e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
                classifierEndpoint e bundle pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sourceRow with
        | intro e endpointData =>
            exact Exists.intro e
              (And.intro endpointData.left
                (hsame_trans (hsame_symm sameRows) endpointData.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro transported.left
      (And.intro transported.right.left
        (And.intro transported.right.right.left
          (And.intro transported.right.right.right
            transported.left.right.right.right.right.right.right.right.right.right))))

theorem ToposFiniteCarrier_subobject_classifier_pullback_boundary [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobject comparison ledger provenance endpoint
      classifierEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
        provenance endpoint bundle pkg ->
      ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject ledger
        provenance classifierEndpoint bundle pkg ->
      hsame provenance classifierEndpoint ->
        ToposFiniteCarrier category sheaf finiteLimit exponential subobject comparison ledger
            classifierEndpoint endpoint bundle pkg ∧
          Cont comparison classifierEndpoint endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier ledgerRows sameProvenanceClassifier
  obtain ⟨transportedCarrier, _categorySheafRow, _finiteExponentialRow,
    _subobjectLedgerRow⟩ :=
    ToposFiniteCarrier_site_sheaf_classifier_obligation carrier ledgerRows
      sameProvenanceClassifier
  have classifierEndpointRow : Cont comparison classifierEndpoint endpoint :=
    transportedCarrier.right.right.right.right.right.right.right.right.left
  have packageEndpointRow : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  exact And.intro transportedCarrier (And.intro classifierEndpointRow packageEndpointRow)

theorem ToposFiniteCarrier_finite_limit_exponential_scope [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobjectClassifier comparison ledger provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier comparison
        ledger provenance endpoint bundle pkg ->
      UnaryHistory finiteLimit ∧ UnaryHistory exponential ∧ UnaryHistory subobjectClassifier ∧
        Cont finiteLimit exponential ledger ∧ Cont ledger subobjectClassifier provenance ∧
          Cont comparison provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrierData
  have finiteLimitUnary : UnaryHistory finiteLimit := carrierData.right.right.left
  have exponentialUnary : UnaryHistory exponential := carrierData.right.right.right.left
  have subobjectClassifierUnary : UnaryHistory subobjectClassifier :=
    carrierData.right.right.right.right.left
  have ledgerRow : Cont finiteLimit exponential ledger :=
    carrierData.right.right.right.right.right.right.left
  have provenanceRow : Cont ledger subobjectClassifier provenance :=
    carrierData.right.right.right.right.right.right.right.left
  have endpointRow : Cont comparison provenance endpoint :=
    carrierData.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrierData.right.right.right.right.right.right.right.right.right
  exact
    ⟨finiteLimitUnary, exponentialUnary, subobjectClassifierUnary, ledgerRow, provenanceRow,
      endpointRow, pkgSig⟩

theorem ToposFiniteCarrier_classified_boundary_transport [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobjectClassifier comparison ledger provenance
      endpoint category' sheaf' finiteLimit' exponential' subobjectClassifier' comparison'
      ledger' provenance' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposFiniteCarrier category sheaf finiteLimit exponential subobjectClassifier comparison
        ledger provenance endpoint bundle pkg ->
      hsame category category' ->
      hsame sheaf sheaf' ->
      hsame finiteLimit finiteLimit' ->
      hsame exponential exponential' ->
      hsame subobjectClassifier subobjectClassifier' ->
      Cont category' sheaf' comparison' ->
      Cont finiteLimit' exponential' ledger' ->
      Cont ledger' subobjectClassifier' provenance' ->
      Cont comparison' provenance' endpoint' ->
      PkgSig bundle endpoint' pkg ->
      ToposFiniteCarrier category' sheaf' finiteLimit' exponential' subobjectClassifier'
          comparison' ledger' provenance' endpoint' bundle pkg ∧
        hsame comparison comparison' ∧ hsame ledger ledger' ∧
          hsame provenance provenance' ∧ hsame endpoint endpoint' := by
  intro carrier sameCategory sameSheaf sameFiniteLimit sameExponential
    sameSubobjectClassifier categorySheafRow finiteExponentialRow ledgerSubobjectRow
    comparisonProvenanceRow pkgRow
  obtain ⟨categoryUnary, sheafUnary, finiteLimitUnary, exponentialUnary,
    subobjectClassifierUnary, oldCategorySheafRow, oldFiniteExponentialRow,
    oldLedgerSubobjectRow, oldComparisonProvenanceRow, _oldPkgRow⟩ := carrier
  have categoryUnary' : UnaryHistory category' :=
    unary_transport categoryUnary sameCategory
  have sheafUnary' : UnaryHistory sheaf' :=
    unary_transport sheafUnary sameSheaf
  have finiteLimitUnary' : UnaryHistory finiteLimit' :=
    unary_transport finiteLimitUnary sameFiniteLimit
  have exponentialUnary' : UnaryHistory exponential' :=
    unary_transport exponentialUnary sameExponential
  have subobjectClassifierUnary' : UnaryHistory subobjectClassifier' :=
    unary_transport subobjectClassifierUnary sameSubobjectClassifier
  have sameComparison : hsame comparison comparison' :=
    cont_respects_hsame sameCategory sameSheaf oldCategorySheafRow categorySheafRow
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameFiniteLimit sameExponential oldFiniteExponentialRow
      finiteExponentialRow
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameLedger sameSubobjectClassifier oldLedgerSubobjectRow
      ledgerSubobjectRow
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameComparison sameProvenance oldComparisonProvenanceRow
      comparisonProvenanceRow
  exact And.intro
    (And.intro categoryUnary'
      (And.intro sheafUnary'
        (And.intro finiteLimitUnary'
          (And.intro exponentialUnary'
            (And.intro subobjectClassifierUnary'
              (And.intro categorySheafRow
                (And.intro finiteExponentialRow
                  (And.intro ledgerSubobjectRow
                    (And.intro comparisonProvenanceRow pkgRow)))))))))
    (And.intro sameComparison
      (And.intro sameLedger (And.intro sameProvenance sameEndpoint)))

theorem ToposSubobjectClassifierLedger_site_sheaf_classifier_obligation [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobject contRows provenance endpoint category' sheaf'
      finiteLimit' exponential' subobject' endpoint' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject contRows
        provenance endpoint probe pkg ->
      hsame category category' -> hsame sheaf sheaf' -> hsame exponential exponential' ->
        Cont category' sheaf' finiteLimit' -> Cont finiteLimit' exponential' subobject' ->
          Cont subobject' contRows endpoint' -> PkgSig probe provenance pkg ->
            ToposSubobjectClassifierLedger category' sheaf' finiteLimit' exponential' subobject'
                contRows provenance endpoint' probe pkg ∧
              hsame finiteLimit finiteLimit' ∧ hsame subobject subobject' ∧
                hsame endpoint endpoint' := by
  intro ledger sameCategory sameSheaf sameExponential categorySheafRow finiteExponentialRow
    subobjectEndpointRow pkgSig'
  obtain ⟨categoryUnary, sheafUnary, finiteLimitUnary, exponentialUnary, subobjectUnary,
    endpointUnary, categorySheafSource, finiteExponentialSource, subobjectEndpointSource,
    pkgSig⟩ := ledger
  have categoryUnary' : UnaryHistory category' :=
    unary_transport categoryUnary sameCategory
  have sheafUnary' : UnaryHistory sheaf' :=
    unary_transport sheafUnary sameSheaf
  have finiteLimitSame : hsame finiteLimit finiteLimit' :=
    cont_respects_hsame sameCategory sameSheaf categorySheafSource categorySheafRow
  have finiteLimitUnary' : UnaryHistory finiteLimit' :=
    unary_transport finiteLimitUnary finiteLimitSame
  have exponentialUnary' : UnaryHistory exponential' :=
    unary_transport exponentialUnary sameExponential
  have subobjectSame : hsame subobject subobject' :=
    cont_respects_hsame finiteLimitSame sameExponential finiteExponentialSource
      finiteExponentialRow
  have subobjectUnary' : UnaryHistory subobject' :=
    unary_transport subobjectUnary subobjectSame
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame subobjectSame (hsame_refl contRows) subobjectEndpointSource
      subobjectEndpointRow
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary endpointSame
  exact And.intro
    (And.intro categoryUnary'
      (And.intro sheafUnary'
        (And.intro finiteLimitUnary'
          (And.intro exponentialUnary'
            (And.intro subobjectUnary'
              (And.intro endpointUnary'
                (And.intro categorySheafRow
                  (And.intro finiteExponentialRow
                    (And.intro subobjectEndpointRow pkgSig')))))))))
    (And.intro finiteLimitSame (And.intro subobjectSame endpointSame))

theorem ToposSubobjectClassifierLedger_pullback_boundary_certificate [AskSetup] [PackageSetup]
    {category sheaf finiteLimit exponential subobject contRows provenance classifierEndpoint
      pullbackEndpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject contRows
        provenance classifierEndpoint probe pkg ->
      Cont classifierEndpoint finiteLimit pullbackEndpoint ->
        SemanticNameCert
            (fun row : BHist =>
              ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject
                  contRows provenance classifierEndpoint probe pkg ∧ hsame row pullbackEndpoint)
            (fun row : BHist =>
              ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject
                  contRows provenance classifierEndpoint probe pkg ∧ hsame row pullbackEndpoint)
            (fun row : BHist =>
              ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject
                  contRows provenance classifierEndpoint probe pkg ∧ hsame row pullbackEndpoint)
            hsame ∧
          Cont category sheaf finiteLimit ∧ Cont finiteLimit exponential subobject ∧
            Cont subobject contRows classifierEndpoint ∧
              Cont classifierEndpoint finiteLimit pullbackEndpoint := by
  intro ledger pullbackRow
  obtain ⟨_categoryUnary, _sheafUnary, _finiteLimitUnary, _exponentialUnary,
    _subobjectUnary, _endpointUnary, categorySheafRow, finiteExponentialRow,
    subobjectClassifierRow, _pkgSig⟩ :=
      ToposSubobjectClassifierLedger_exactness ledger
  have pullbackSource :
      (fun row : BHist =>
        ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject contRows
            provenance classifierEndpoint probe pkg ∧ hsame row pullbackEndpoint)
          pullbackEndpoint :=
    And.intro ledger (hsame_refl pullbackEndpoint)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject contRows
                provenance classifierEndpoint probe pkg ∧ hsame row pullbackEndpoint)
          (fun row : BHist =>
            ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject contRows
                provenance classifierEndpoint probe pkg ∧ hsame row pullbackEndpoint)
          (fun row : BHist =>
            ToposSubobjectClassifierLedger category sheaf finiteLimit exponential subobject contRows
                provenance classifierEndpoint probe pkg ∧ hsame row pullbackEndpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro pullbackEndpoint pullbackSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro categorySheafRow
      (And.intro finiteExponentialRow (And.intro subobjectClassifierRow pullbackRow)))

end BEDC.Derived.ToposUp
