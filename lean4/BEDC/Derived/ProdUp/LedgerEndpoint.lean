import BEDC.Derived.ProdUp.ComponentwiseRefinement

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

inductive ProdHistoryLedgerChain (Left Right : BHist -> Prop) : BHist -> BHist -> Prop where
  | step {rho z : BHist} :
      ProdHistoryLedgerPolicy Left Right rho z ->
        ProdHistoryLedgerChain Left Right rho z
  | cons {rho v z : BHist} :
      ProdHistoryLedgerPolicy Left Right rho v ->
        ProdHistoryLedgerChain Left Right v z ->
          ProdHistoryLedgerChain Left Right rho z

theorem ProdHistoryLedgerChain_trans {Left Right : BEDC.FKernel.Hist.BHist → Prop}
    {rho mid z : BEDC.FKernel.Hist.BHist} :
    BEDC.Derived.ProdUp.ProdHistoryLedgerChain Left Right rho mid →
      BEDC.Derived.ProdUp.ProdHistoryLedgerChain Left Right mid z →
        BEDC.Derived.ProdUp.ProdHistoryLedgerChain Left Right rho z := by
  intro first
  induction first generalizing z with
  | step ledger =>
      intro second
      exact BEDC.Derived.ProdUp.ProdHistoryLedgerChain.cons ledger second
  | cons ledger _ ih =>
      intro second
      exact BEDC.Derived.ProdUp.ProdHistoryLedgerChain.cons ledger (ih second)

theorem ProdHistoryLedgerPolicy_classifier_endpoint_equivalence {Left Right : BHist → Prop}
    {rho v w : BHist} :
    ProdHistoryLedgerPolicy Left Right rho v →
      (ProdHistoryClassifier Left Right rho w ↔ ProdHistoryClassifier Left Right v w) := by
  intro ledger
  constructor
  · intro rawTarget
    exact ProdHistoryClassifier_trans
      (ProdHistoryClassifier_symm (ProdHistoryLedgerPolicy_raw_visible_classifier ledger))
      rawTarget
  · intro visibleTarget
    exact ProdHistoryLedgerPolicy_classifier_extension ledger visibleTarget

theorem ProdHistoryLedgerPolicy_two_step_classifier_endpoint_equivalence
    {Left Right : BHist -> Prop} {rho v w z : BHist} :
    ProdHistoryLedgerPolicy Left Right rho v ->
      ProdHistoryLedgerPolicy Left Right v w ->
        (ProdHistoryClassifier Left Right rho z <-> ProdHistoryClassifier Left Right w z) := by
  intro firstLedger secondLedger
  have rhoW : ProdHistoryClassifier Left Right rho w :=
    ProdHistoryLedgerPolicy_two_step_classifier_composition firstLedger secondLedger
  constructor
  · intro rhoZ
    exact ProdHistoryClassifier_trans (ProdHistoryClassifier_symm rhoW) rhoZ
  · intro wZ
    exact ProdHistoryClassifier_trans rhoW wZ

theorem ProdHistoryLedgerChain_envelope_closure {Left Right : BHist -> Prop} {rho z : BHist} :
    ProdHistoryLedgerChain Left Right rho z ->
      ProdHistoryCarrier Left Right z /\
        ProdHistoryClassifier Left Right rho z /\
          (forall w : BHist,
            (ProdHistoryClassifier Left Right rho w <->
              ProdHistoryClassifier Left Right z w) /\
              (ProdHistoryClassifier Left Right w rho <->
                ProdHistoryClassifier Left Right w z)) := by
  intro chain
  induction chain with
  | step ledger =>
      have rhoZ :=
        ProdHistoryLedgerPolicy_raw_visible_classifier ledger
      constructor
      · exact ProdHistoryLedgerPolicy_visible_carrier ledger
      · constructor
        · exact rhoZ
        · intro w
          have endpoint :=
            ProdHistoryLedgerPolicy_classifier_endpoint_equivalence (w := w) ledger
          constructor
          · exact endpoint
          · constructor
            · intro wRho
              exact ProdHistoryClassifier_trans wRho rhoZ
            · intro wZ
              exact ProdHistoryClassifier_trans wZ (ProdHistoryClassifier_symm rhoZ)
  | cons ledger _ ih =>
      cases ih with
      | intro carrierZ rest =>
          cases rest with
          | intro vZ endpointZ =>
              have rhoV :=
                ProdHistoryLedgerPolicy_raw_visible_classifier ledger
              have rhoZ :=
                ProdHistoryClassifier_trans rhoV vZ
              constructor
              · exact carrierZ
              · constructor
                · exact rhoZ
                · intro w
                  have endpointV :=
                    ProdHistoryLedgerPolicy_classifier_endpoint_equivalence (w := w) ledger
                  have tailEndpoint := endpointZ w
                  cases tailEndpoint with
                  | intro tailLeft tailRight =>
                      constructor
                      · constructor
                        · intro rhoW
                          exact Iff.mp tailLeft (Iff.mp endpointV rhoW)
                        · intro zW
                          exact Iff.mpr endpointV (Iff.mpr tailLeft zW)
                      · constructor
                        · intro wRho
                          exact ProdHistoryClassifier_trans wRho rhoZ
                        · intro wZ
                          exact ProdHistoryClassifier_trans wZ (ProdHistoryClassifier_symm rhoZ)

theorem ProdHistoryLedgerChain_shared_raw_visible_classifier {Left Right : BHist -> Prop}
    {raw visible visible' : BHist} :
    ProdHistoryLedgerChain Left Right raw visible ->
      ProdHistoryLedgerChain Left Right raw visible' ->
        ProdHistoryClassifier Left Right visible visible' := by
  intro leftChain rightChain
  have leftEnvelope := ProdHistoryLedgerChain_envelope_closure leftChain
  have rightEnvelope := ProdHistoryLedgerChain_envelope_closure rightChain
  exact ProdHistoryClassifier_trans
    (ProdHistoryClassifier_symm leftEnvelope.right.left)
    rightEnvelope.right.left

theorem ProdHistoryLedgerChain_boundary_classifier_decomposition
    {Left Right : BHist -> Prop} {rho z : BHist} :
    ProdHistoryLedgerChain Left Right rho z ->
      (∃ l r : BHist, Left l ∧ Right r ∧ Cont l r z) ∧
        (((ProdHistoryLedgerPolicy Left Right rho z) ∨
            ∃ v : BHist,
              ProdHistoryLedgerPolicy Left Right rho v ∧
                ProdHistoryClassifier Left Right v z) ∧
          ((ProdHistoryLedgerPolicy Left Right rho z) ∨
            ∃ v : BHist,
              ProdHistoryClassifier Left Right rho v ∧
                ProdHistoryLedgerPolicy Left Right v z)) := by
  intro chain
  induction chain with
  | step ledger =>
      have visibleCarrier :=
        ProdHistoryLedgerPolicy_visible_carrier ledger
      exact And.intro visibleCarrier
        (And.intro (Or.inl ledger) (Or.inl ledger))
  | cons ledger tail tailData =>
      have tailEnvelope := ProdHistoryLedgerChain_envelope_closure tail
      have rawVisibleClassifier :=
        ProdHistoryLedgerPolicy_raw_visible_classifier ledger
      have terminalClassifier :=
        ProdHistoryClassifier_trans rawVisibleClassifier tailEnvelope.right.left
      have terminalPolicy :=
        tailData.right.right
      cases terminalPolicy with
      | inl lastLedger =>
          exact And.intro tailData.left
            (And.intro
              (Or.inr
                (Exists.intro _
                  (And.intro ledger tailEnvelope.right.left)))
              (Or.inr
                (Exists.intro _
                  (And.intro rawVisibleClassifier lastLedger))))
      | inr tailWitness =>
          cases tailWitness with
          | intro v data =>
              exact And.intro tailData.left
                (And.intro
                  (Or.inr
                    (Exists.intro _
                      (And.intro ledger tailEnvelope.right.left)))
                  (Or.inr
                    (Exists.intro v
                      (And.intro
                        (ProdHistoryClassifier_trans rawVisibleClassifier
                          data.left)
                        data.right))))

theorem ProdHistoryLedgerPolicy_visible_empty_component_exposure {Left Right : BHist -> Prop}
    {rho : BHist} :
    ProdHistoryLedgerPolicy Left Right rho BHist.Empty ->
      exists l : BHist, exists r : BHist,
        Left l /\ Right r /\ hsame l BHist.Empty /\ hsame r BHist.Empty /\
          ProdHistoryClassifier Left Right rho BHist.Empty := by
  intro ledger
  have visibleCarrier : ProdHistoryCarrier Left Right BHist.Empty :=
    ProdHistoryLedgerPolicy_visible_carrier ledger
  have visibleComponents :=
    ProdHistoryCarrier_empty_result_components visibleCarrier
  have rawVisibleClassifier : ProdHistoryClassifier Left Right rho BHist.Empty :=
    ProdHistoryLedgerPolicy_raw_visible_classifier ledger
  cases visibleComponents with
  | intro l rest =>
      cases rest with
      | intro r data =>
          cases data with
          | intro leftCarrier data =>
              cases data with
              | intro rightCarrier data =>
                  cases data with
                  | intro sameLeft sameRight =>
                      exact Exists.intro l
                        (Exists.intro r
                          (And.intro leftCarrier
                            (And.intro rightCarrier
                              (And.intro sameLeft
                                (And.intro sameRight rawVisibleClassifier)))))

theorem ProdHistoryLedgerChain_displayed_component_readback
    {Left Right : BHist -> Prop} {LeftEq RightEq : BHist -> BHist -> Prop}
    (coherent : ProdPairRepCoherent Left Right LeftEq RightEq) {rho z l r : BHist} :
    ProdHistoryLedgerChain Left Right rho z ->
      ProdPairRep Left Right rho l r ->
        ∃ l' : BHist, ∃ r' : BHist,
          ProdPairRep Left Right z l' r' ∧ LeftEq l l' ∧ RightEq r r' := by
  intro chain repRho
  have envelope := ProdHistoryLedgerChain_envelope_closure chain
  have carrierZ : ProdHistoryCarrier Left Right z := envelope.left
  have classifierRhoZ : ProdHistoryClassifier Left Right rho z := envelope.right.left
  have sameRhoZ : hsame rho z := classifierRhoZ.right.right
  have displayedZ :
      ∃ l' : BHist, ∃ r' : BHist, ProdPairRep Left Right z l' r' :=
    Iff.mp (ProdPairRep_coverage (Left := Left) (Right := Right) (h := z)) carrierZ
  cases displayedZ with
  | intro l' rest =>
      cases rest with
      | intro r' repZ =>
          have components : LeftEq l l' ∧ RightEq r r' :=
            ProdPairRep_hsame_coherence coherent repRho repZ sameRhoZ
          exact Exists.intro l'
            (Exists.intro r'
              (And.intro repZ (And.intro components.left components.right)))

theorem ProdHistoryLedgerChain_componentwise_classifier_endpoint_equivalence
    {Left Right : BHist -> Prop} {LeftEq RightEq : BHist -> BHist -> Prop}
    {rho z : BHist} :
    ProdHistoryLedgerChain Left Right rho z ->
      forall w : BHist,
        (ProdComponentHistoryClassifier Left Right LeftEq RightEq rho w <->
          ProdComponentHistoryClassifier Left Right LeftEq RightEq z w) /\
          (ProdComponentHistoryClassifier Left Right LeftEq RightEq w rho <->
            ProdComponentHistoryClassifier Left Right LeftEq RightEq w z) := by
  intro chain w
  have envelope := ProdHistoryLedgerChain_envelope_closure chain
  have classifiedRhoZ : ProdHistoryClassifier Left Right rho z := envelope.right.left
  have sameRhoZ : hsame rho z := classifiedRhoZ.right.right
  constructor
  · constructor
    · intro classifier
      exact ProdComponentHistoryClassifier_hsame_transport sameRhoZ (hsame_refl w) classifier
    · intro classifier
      exact ProdComponentHistoryClassifier_hsame_transport
        (hsame_symm sameRhoZ) (hsame_refl w) classifier
  · constructor
    · intro classifier
      exact ProdComponentHistoryClassifier_hsame_transport (hsame_refl w) sameRhoZ classifier
    · intro classifier
      exact ProdComponentHistoryClassifier_hsame_transport
        (hsame_refl w) (hsame_symm sameRhoZ) classifier

theorem ProdHistoryLedgerChain_public_certificate_component_readback
    {Left Right : BHist -> Prop} {LeftEq RightEq : BHist -> BHist -> Prop}
    (leftCert : NameCert Left LeftEq) (rightCert : NameCert Right RightEq)
    (coherent : ProdPairRepCoherent Left Right LeftEq RightEq) {rho z l r : BHist} :
    ProdHistoryLedgerChain Left Right rho z ->
      ProdPairRep Left Right rho l r ->
        SemanticNameCert (ProdHistoryCarrier Left Right) (ProdHistoryCarrier Left Right)
            (ProdHistoryCarrier Left Right)
            (ProdComponentHistoryClassifier Left Right LeftEq RightEq) ∧
          ProdHistoryClassifier Left Right rho z ∧
            ∃ l' r' : BHist,
              ProdPairRep Left Right z l' r' ∧ LeftEq l l' ∧ RightEq r r' := by
  intro chain repRho
  have certificate :=
    ProdComponentHistoryClassifier_semantic_name_certificate leftCert rightCert coherent
  have envelope := ProdHistoryLedgerChain_envelope_closure chain
  have readback :=
    ProdHistoryLedgerChain_displayed_component_readback coherent chain repRho
  exact And.intro certificate (And.intro envelope.right.left readback)

end BEDC.Derived.ProdUp
