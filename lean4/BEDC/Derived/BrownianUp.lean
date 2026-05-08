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

theorem BrownianStepContinuityClassifier_namecert_obligation_surface
    {martingale continuous time path step normal provenance ledger : BHist} :
    BrownianStepContinuityClassifier martingale continuous time path step normal provenance ledger ->
      SemanticNameCert
        (fun e : BHist =>
          exists p n : BHist,
            BrownianStepContinuityClassifier martingale continuous time path step n p e)
        (fun e : BHist =>
          exists p n : BHist,
            BrownianStepContinuityClassifier martingale continuous time path step n p e)
        (fun e : BHist =>
          exists p n : BHist,
            BrownianStepContinuityClassifier martingale continuous time path step n p e)
        (fun left right : BHist =>
          (exists lp ln : BHist,
            BrownianStepContinuityClassifier martingale continuous time path step ln lp left) /\
          (exists rp rn : BHist,
            BrownianStepContinuityClassifier martingale continuous time path step rn rp right) /\
          hsame left right) := by
  intro classified
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro ledger (Exists.intro provenance (Exists.intro normal classified))
      equiv_refl := by
        intro h source
        exact And.intro source (And.intro source (hsame_refl h))
      equiv_symm := by
        intro h k row
        exact And.intro row.right.left (And.intro row.left (hsame_symm row.right.right))
      equiv_trans := by
        intro h k r rowHK rowKR
        exact And.intro rowHK.left
          (And.intro rowKR.right.left (hsame_trans rowHK.right.right rowKR.right.right))
      carrier_respects_equiv := by
        intro h k row _source
        exact row.right.left
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

end BEDC.Derived.BrownianUp
