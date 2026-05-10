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

theorem BrownianStepContinuityClassifier_classifier_stability
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
                        hsame step step' ∧ hsame provenance provenance' ∧
                          hsame ledger ledger' := by
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
    (And.intro sameStep (And.intro sameProvenance sameLedger))

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

theorem BrownianStepContinuityClassifier_path_step_boundary_exhaustion
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
                        hsame step step' ∧ hsame provenance provenance' ∧ hsame ledger ledger' ∧
                          UnaryHistory time' ∧ UnaryHistory normal' := by
  intro classified sameMartingale sameContinuous sameTime samePath sameNormal stepRow provenanceRow
    ledgerRow
  have transported :
      BrownianStepContinuityClassifier martingale' continuous' time' path' step' normal'
          provenance' ledger' ∧ hsame provenance provenance' ∧ hsame ledger ledger' :=
    BrownianStepContinuityClassifier_step_ledger_transport classified sameMartingale sameContinuous
      sameTime samePath sameNormal stepRow provenanceRow ledgerRow
  have sameStep : hsame step step' :=
    cont_respects_hsame sameContinuous samePath classified.right.right.right.right.right.left
      stepRow
  constructor
  · exact transported.left
  · constructor
    · exact sameStep
    · constructor
      · exact transported.right.left
      · constructor
        · exact transported.right.right
        · constructor
          · exact transported.left.right.right.left
          · exact transported.left.right.right.right.right.left

theorem BrownianStepContinuityClassifier_gaussian_step_ledger_coverage
    {martingale continuous time path step normal provenance ledger step' provenance' ledger' :
      BHist} :
    BrownianStepContinuityClassifier martingale continuous time path step normal provenance
        ledger ->
      Cont continuous path step' ->
        Cont martingale step' provenance' ->
          Cont provenance' normal ledger' ->
            UnaryHistory time ∧ UnaryHistory normal ∧ UnaryHistory step' ∧
              hsame step step' ∧ hsame provenance provenance' ∧ hsame ledger ledger' ∧
                hsame step' (append continuous path) ∧
                  hsame ledger' (append provenance' normal) := by
  intro classified stepRow provenanceRow ledgerRow
  have stepUnary : UnaryHistory step' :=
    unary_cont_closed classified.right.left classified.right.right.right.left stepRow
  have sameStep : hsame step step' :=
    cont_respects_hsame (hsame_refl continuous) (hsame_refl path)
      classified.right.right.right.right.right.left stepRow
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame (hsame_refl martingale) sameStep
      classified.right.right.right.right.right.right.left provenanceRow
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameProvenance (hsame_refl normal)
      classified.right.right.right.right.right.right.right ledgerRow
  exact And.intro classified.right.right.left
    (And.intro classified.right.right.right.right.left
      (And.intro stepUnary
        (And.intro sameStep
          (And.intro sameProvenance
            (And.intro sameLedger (And.intro stepRow ledgerRow))))))

theorem BrownianStepContinuityClassifier_path_continuity_ledger_exactness
    {martingale continuous time path step normal provenance ledger pathLedger endpoint : BHist} :
    BrownianStepContinuityClassifier martingale continuous time path step normal provenance ledger ->
      Cont continuous path pathLedger ->
        Cont pathLedger ledger endpoint ->
          UnaryHistory continuous ∧ UnaryHistory path ∧ UnaryHistory pathLedger ∧
            UnaryHistory endpoint ∧ hsame pathLedger (append continuous path) ∧
              hsame endpoint (append pathLedger ledger) := by
  intro classified pathRow endpointRow
  have pathLedgerUnary : UnaryHistory pathLedger :=
    unary_cont_closed classified.right.left classified.right.right.right.left pathRow
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed
      (unary_cont_closed classified.left
        (unary_cont_closed classified.right.left classified.right.right.right.left
          classified.right.right.right.right.right.left)
        classified.right.right.right.right.right.right.left)
      classified.right.right.right.right.left
      classified.right.right.right.right.right.right.right
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed pathLedgerUnary ledgerUnary endpointRow
  exact And.intro classified.right.left
    (And.intro classified.right.right.right.left
      (And.intro pathLedgerUnary
        (And.intro endpointUnary
          (And.intro pathRow endpointRow))))

theorem BrownianStepContinuityClassifier_ledger_exactness
    {martingale continuous time path step normal provenance ledger publicRow : BHist} :
    BrownianStepContinuityClassifier martingale continuous time path step normal provenance ledger ->
      Cont ledger path publicRow ->
        UnaryHistory step ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
          UnaryHistory publicRow ∧ hsame step (append continuous path) ∧
            hsame provenance (append martingale step) ∧ hsame ledger (append provenance normal) ∧
              hsame publicRow (append ledger path) := by
  intro classified publicRowCont
  have stepUnary : UnaryHistory step :=
    unary_cont_closed classified.right.left classified.right.right.right.left
      classified.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed classified.left stepUnary
      classified.right.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed provenanceUnary classified.right.right.right.right.left
      classified.right.right.right.right.right.right.right
  have publicRowUnary : UnaryHistory publicRow :=
    unary_cont_closed ledgerUnary classified.right.right.right.left publicRowCont
  exact And.intro stepUnary
    (And.intro provenanceUnary
      (And.intro ledgerUnary
        (And.intro publicRowUnary
          (And.intro classified.right.right.right.right.right.left
            (And.intro classified.right.right.right.right.right.right.left
              (And.intro classified.right.right.right.right.right.right.right publicRowCont))))))

theorem BrownianStepContinuityClassifier_continuous_path_projection
    {martingale continuous time path step normal provenance ledger pathLedger endpoint : BHist} :
    BrownianStepContinuityClassifier martingale continuous time path step normal provenance ledger ->
      Cont continuous path pathLedger ->
        Cont pathLedger ledger endpoint ->
          UnaryHistory martingale ∧ UnaryHistory continuous ∧ UnaryHistory path ∧
            UnaryHistory pathLedger ∧ UnaryHistory endpoint ∧
              Cont continuous path pathLedger ∧ Cont pathLedger ledger endpoint ∧
                hsame pathLedger (append continuous path) ∧
                  hsame endpoint (append pathLedger ledger) ∧
                    hsame provenance (append martingale step) := by
  intro classified pathRow endpointRow
  have surface :=
    BrownianStepContinuityClassifier_dependency_surface classified
  have pathExact :=
    BrownianStepContinuityClassifier_path_continuity_ledger_exactness classified pathRow
      endpointRow
  exact And.intro surface.left
    (And.intro surface.right.left
      (And.intro surface.right.right.right.left
        (And.intro pathExact.right.right.left
          (And.intro pathExact.right.right.right.left
            (And.intro pathRow
              (And.intro endpointRow
                 (And.intro pathExact.right.right.right.right.left
                   (And.intro pathExact.right.right.right.right.right
                     surface.right.right.right.right.right.right.right.right.right.left))))))))

end BEDC.Derived.BrownianUp
