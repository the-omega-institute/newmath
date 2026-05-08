import BEDC.Derived.AdeleUp
import BEDC.Derived.NumFieldUp
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClassFieldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.AdeleUp
open BEDC.Derived.NumFieldUp
open BEDC.Derived.RatUp

theorem ClassFieldCarrierClassifier_obligation
    {base base' idele idele' carrier carrier' : BHist} :
    NumFieldReflexiveRationalCarrier base -> RatHistoryClassifier base base' ->
      AdeleHistoryCarrier idele -> hsame idele idele' -> Cont base idele carrier ->
        Cont base' idele' carrier' ->
          NumFieldReflexiveRationalCarrier base' ∧ AdeleHistoryCarrier idele' ∧
            hsame carrier carrier' := by
  intro baseCarrier baseClassified ideleCarrier sameIdele leftCont rightCont
  have numCert :
      SemanticNameCert NumFieldReflexiveRationalCarrier NumFieldReflexiveRationalCarrier
        NumFieldReflexiveRationalCarrier RatHistoryClassifier :=
    NumFieldReflexiveRational_semantic_name_certificate
  have adeleCert :
      SemanticNameCert AdeleHistoryCarrier AdeleHistoryCarrier AdeleHistoryCarrier hsame :=
    AdeleHistoryCarrier_semanticNameCert
  have baseCarrier' : NumFieldReflexiveRationalCarrier base' :=
    numCert.core.carrier_respects_equiv baseClassified baseCarrier
  have ideleCarrier' : AdeleHistoryCarrier idele' :=
    adeleCert.core.carrier_respects_equiv sameIdele ideleCarrier
  have sameCarrier : hsame carrier carrier' :=
    cont_respects_hsame baseClassified.right.right sameIdele leftCont rightCont
  exact And.intro baseCarrier' (And.intro ideleCarrier' sameCarrier)

theorem ClassFieldArtinFrobenius_stability_obligation
    {base base' idele idele' extension extension' artin artin' frob frob' : BHist} :
    NumFieldReflexiveRationalCarrier base -> RatHistoryClassifier base base' ->
      AdeleHistoryCarrier idele -> hsame idele idele' -> Cont base idele extension ->
        Cont base' idele' extension' -> Cont idele extension artin ->
          Cont idele' extension' artin' -> Cont extension base frob ->
            Cont extension' base' frob' ->
              hsame extension extension' ∧ hsame artin artin' ∧ hsame frob frob' := by
  intro _baseCarrier baseClassified _ideleCarrier sameIdele leftExtension rightExtension
    leftArtin rightArtin leftFrob rightFrob
  have sameExtension : hsame extension extension' :=
    cont_respects_hsame baseClassified.right.right sameIdele leftExtension rightExtension
  have sameArtin : hsame artin artin' :=
    cont_respects_hsame sameIdele sameExtension leftArtin rightArtin
  have sameFrob : hsame frob frob' :=
    cont_respects_hsame sameExtension baseClassified.right.right leftFrob rightFrob
  exact And.intro sameExtension (And.intro sameArtin sameFrob)

def ClassFieldSourceCarrier
    (numField adele extension classifier ledger : BHist) : Prop :=
  UnaryHistory numField ∧ UnaryHistory adele ∧ Cont numField adele extension ∧
    hsame classifier extension ∧ UnaryHistory ledger

theorem ClassFieldSourceCarrier_semantic_name_certificate
    {numField adele extension classifier ledger : BHist} :
    ClassFieldSourceCarrier numField adele extension classifier ledger ->
      SemanticNameCert
        (fun h : BHist => ClassFieldSourceCarrier numField adele h classifier ledger)
        (fun h : BHist => ClassFieldSourceCarrier numField adele h classifier ledger)
        (fun h : BHist => ClassFieldSourceCarrier numField adele h classifier ledger)
        hsame := by
  intro source
  exact {
    core := {
      carrier_inhabited := Exists.intro extension source
      equiv_refl := by
        intro h _sourceH
        exact hsame_refl h
      equiv_symm := by
        intro _h _k sameHK
        exact hsame_symm sameHK
      equiv_trans := by
        intro _h _k _r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        have routeK : Cont numField adele k :=
          cont_result_hsame_transport sourceH.right.right.left sameHK
        have classifierK : hsame classifier k :=
          hsame_trans sourceH.right.right.right.left sameHK
        exact ⟨sourceH.left, sourceH.right.left, routeK, classifierK,
          sourceH.right.right.right.right⟩
    }
    pattern_sound := by
      intro _h sourceH
      exact sourceH
    ledger_sound := by
      intro _h sourceH
      exact sourceH
  }

def ClassFieldArtinFrobeniusRows
    (base idele extension artin frob : BHist) : Prop :=
  UnaryHistory base ∧ UnaryHistory idele ∧ UnaryHistory artin ∧
    Cont idele artin frob ∧ Cont base frob extension

theorem ClassFieldArtinFrobeniusRows_ledger_exactness
    {base idele extension artin frob : BHist} :
    ClassFieldArtinFrobeniusRows base idele extension artin frob ->
      UnaryHistory base ∧ UnaryHistory idele ∧ UnaryHistory artin ∧
        Cont idele artin frob ∧ Cont base frob extension ∧
          hsame (append idele artin) frob ∧ hsame (append base frob) extension := by
  intro rows
  have frobReadback : hsame (append idele artin) frob := by
    cases rows.right.right.right.left
    exact hsame_refl (append idele artin)
  have extensionReadback : hsame (append base frob) extension := by
    cases rows.right.right.right.right
    exact hsame_refl (append base frob)
  exact And.intro rows.left
    (And.intro rows.right.left
      (And.intro rows.right.right.left
        (And.intro rows.right.right.right.left
          (And.intro rows.right.right.right.right
            (And.intro frobReadback extensionReadback)))))

theorem ClassFieldArtinFrobeniusRows_stability
    {base idele extension artin frob idele' artin' frob' extension' : BHist} :
    ClassFieldArtinFrobeniusRows base idele extension artin frob ->
      hsame idele idele' -> hsame artin artin' -> hsame frob frob' ->
        hsame extension extension' ->
          ClassFieldArtinFrobeniusRows base idele' extension' artin' frob' ∧
            Cont idele' artin' frob' ∧ Cont base frob' extension' := by
  intro rows sameIdele sameArtin sameFrob sameExtension
  have ideleUnary : UnaryHistory idele' :=
    unary_transport rows.right.left sameIdele
  have artinUnary : UnaryHistory artin' :=
    unary_transport rows.right.right.left sameArtin
  have frobRoute : Cont idele' artin' frob' :=
    cont_hsame_transport sameIdele sameArtin sameFrob rows.right.right.right.left
  have extensionRoute : Cont base frob' extension' :=
    cont_hsame_transport (hsame_refl base) sameFrob sameExtension
      rows.right.right.right.right
  exact And.intro
    (And.intro rows.left
      (And.intro ideleUnary (And.intro artinUnary (And.intro frobRoute extensionRoute))))
    (And.intro frobRoute extensionRoute)

end BEDC.Derived.ClassFieldUp
