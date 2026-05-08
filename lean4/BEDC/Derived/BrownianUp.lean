import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.BrownianUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def BrownianStepContinuityClassifier
    (martingale continuous time path step normal provenance ledger : BHist) : Prop :=
  UnaryHistory martingale ∧ UnaryHistory continuous ∧ UnaryHistory time ∧ UnaryHistory path ∧
    UnaryHistory normal ∧ Cont continuous path step ∧ Cont martingale step provenance ∧
      Cont provenance normal ledger

theorem BrownianStepContinuityClassifier_step_ledger_transport
    {martingale continuous time path step normal provenance ledger martingale' continuous' time'
      path' step' normal' provenance' ledger' : BHist} :
    BrownianStepContinuityClassifier martingale continuous time path step normal provenance ledger ->
      hsame martingale martingale' ->
        hsame continuous continuous' ->
          hsame time time' ->
            hsame path path' ->
              hsame normal normal' ->
                Cont continuous' path' step' ->
                  Cont martingale' step' provenance' ->
                    Cont provenance' normal' ledger' ->
                      BrownianStepContinuityClassifier martingale' continuous' time' path' step'
                          normal' provenance' ledger' ∧
                        hsame provenance provenance' ∧ hsame ledger ledger' := by
  intro classified sameMartingale sameContinuous sameTime samePath sameNormal stepRow provenanceRow
    ledgerRow
  have martingaleUnary : UnaryHistory martingale' :=
    unary_transport classified.left sameMartingale
  have continuousUnary : UnaryHistory continuous' :=
    unary_transport classified.right.left sameContinuous
  have timeUnary : UnaryHistory time' :=
    unary_transport classified.right.right.left sameTime
  have pathUnary : UnaryHistory path' :=
    unary_transport classified.right.right.right.left samePath
  have normalUnary : UnaryHistory normal' :=
    unary_transport classified.right.right.right.right.left sameNormal
  have sameStep : hsame step step' :=
    cont_respects_hsame sameContinuous samePath classified.right.right.right.right.right.left
      stepRow
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameMartingale sameStep classified.right.right.right.right.right.right.left
      provenanceRow
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameProvenance sameNormal
      classified.right.right.right.right.right.right.right ledgerRow
  exact And.intro
    (And.intro martingaleUnary
      (And.intro continuousUnary
        (And.intro timeUnary
          (And.intro pathUnary
            (And.intro normalUnary
              (And.intro stepRow (And.intro provenanceRow ledgerRow)))))))
    (And.intro sameProvenance sameLedger)

theorem BrownianStepContinuityClassifier_dependency_surface
    {martingale continuous time path step normal provenance ledger : BHist} :
    BrownianStepContinuityClassifier martingale continuous time path step normal provenance ledger ->
      UnaryHistory martingale ∧ UnaryHistory continuous ∧ UnaryHistory time ∧
        UnaryHistory path ∧ UnaryHistory normal ∧ Cont continuous path step ∧
          Cont martingale step provenance ∧ Cont provenance normal ledger ∧
            hsame step (append continuous path) ∧ hsame provenance (append martingale step) ∧
              hsame ledger (append provenance normal) := by
  intro classified
  exact And.intro classified.left
    (And.intro classified.right.left
      (And.intro classified.right.right.left
        (And.intro classified.right.right.right.left
          (And.intro classified.right.right.right.right.left
            (And.intro classified.right.right.right.right.right.left
              (And.intro classified.right.right.right.right.right.right.left
                (And.intro classified.right.right.right.right.right.right.right
                  (And.intro classified.right.right.right.right.right.left
                    (And.intro classified.right.right.right.right.right.right.left
                      classified.right.right.right.right.right.right.right)))))))))

theorem BrownianStepContinuityClassifier_semantic_name_certificate
    {martingale continuous time path step normal provenance ledger : BHist} :
    BrownianStepContinuityClassifier martingale continuous time path step normal provenance ledger ->
      SemanticNameCert
          (fun row : BHist => exists carriedProvenance : BHist,
            BrownianStepContinuityClassifier martingale continuous time path step normal
              carriedProvenance row)
          (fun row : BHist => exists carriedProvenance : BHist,
            BrownianStepContinuityClassifier martingale continuous time path step normal
              carriedProvenance row)
          (fun row : BHist => exists carriedProvenance : BHist,
            BrownianStepContinuityClassifier martingale continuous time path step normal
              carriedProvenance row)
          (fun left right : BHist =>
            (exists leftProvenance : BHist,
              BrownianStepContinuityClassifier martingale continuous time path step normal
                leftProvenance left) ∧
              (exists rightProvenance : BHist,
                BrownianStepContinuityClassifier martingale continuous time path step normal
                  rightProvenance right) ∧
                hsame left right) ∧
        Cont continuous path step ∧ Cont martingale step provenance ∧
          Cont provenance normal ledger := by
  intro classified
  have carrierLedger :
      (fun row : BHist => exists carriedProvenance : BHist,
        BrownianStepContinuityClassifier martingale continuous time path step normal
          carriedProvenance row) ledger :=
    Exists.intro provenance classified
  have cert :
      SemanticNameCert
          (fun row : BHist => exists carriedProvenance : BHist,
            BrownianStepContinuityClassifier martingale continuous time path step normal
              carriedProvenance row)
          (fun row : BHist => exists carriedProvenance : BHist,
            BrownianStepContinuityClassifier martingale continuous time path step normal
              carriedProvenance row)
          (fun row : BHist => exists carriedProvenance : BHist,
            BrownianStepContinuityClassifier martingale continuous time path step normal
              carriedProvenance row)
          (fun left right : BHist =>
            (exists leftProvenance : BHist,
              BrownianStepContinuityClassifier martingale continuous time path step normal
                leftProvenance left) ∧
              (exists rightProvenance : BHist,
                BrownianStepContinuityClassifier martingale continuous time path step normal
                  rightProvenance right) ∧
                hsame left right) := {
    core := {
      carrier_inhabited := Exists.intro ledger carrierLedger
      equiv_refl := by
        intro row rowCarrier
        exact And.intro rowCarrier (And.intro rowCarrier (hsame_refl row))
      equiv_symm := by
        intro left right related
        exact And.intro related.right.left
          (And.intro related.left (hsame_symm related.right.right))
      equiv_trans := by
        intro left middle right relatedLM relatedMR
        exact And.intro relatedLM.left
          (And.intro relatedMR.right.left
            (hsame_trans relatedLM.right.right relatedMR.right.right))
      carrier_respects_equiv := by
        intro left right related _leftCarrier
        exact related.right.left
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro classified.right.right.right.right.right.left
      (And.intro classified.right.right.right.right.right.right.left
        classified.right.right.right.right.right.right.right))

end BEDC.Derived.BrownianUp
