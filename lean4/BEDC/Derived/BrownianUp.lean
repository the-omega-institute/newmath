import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BrownianUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

theorem BrownianStepContinuityClassifier_joint_classifier_transport
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
                        UnaryHistory martingale' ∧ UnaryHistory continuous' ∧
                          UnaryHistory time' ∧ UnaryHistory normal' ∧
                            hsame provenance provenance' ∧ hsame ledger ledger' := by
  intro classified sameMartingale sameContinuous sameTime samePath sameNormal stepRow provenanceRow
    ledgerRow
  have transported :
      BrownianStepContinuityClassifier martingale' continuous' time' path' step' normal'
          provenance' ledger' ∧ hsame provenance provenance' ∧ hsame ledger ledger' :=
    BrownianStepContinuityClassifier_step_ledger_transport classified sameMartingale sameContinuous
      sameTime samePath sameNormal stepRow provenanceRow ledgerRow
  exact And.intro transported.left
    (And.intro transported.left.left
      (And.intro transported.left.right.left
        (And.intro transported.left.right.right.left
          (And.intro transported.left.right.right.right.right.left
            (And.intro transported.right.left transported.right.right)))))

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

end BEDC.Derived.BrownianUp
