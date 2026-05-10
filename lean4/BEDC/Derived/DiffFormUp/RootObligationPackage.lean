import BEDC.Derived.DiffFormUp
import BEDC.Derived.DiffFormUp.WedgeProbeConcatenation
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem DiffFormRootCarrierSource_obligation {degree probe tensor scalar antisym ledger : BHist} :
    UnaryHistory degree -> UnaryHistory probe -> Cont degree probe tensor ->
      UnaryHistory antisym -> Cont tensor antisym scalar ->
        hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ->
          UnaryHistory degree ∧ UnaryHistory probe ∧ UnaryHistory tensor ∧
            UnaryHistory scalar ∧
              hsame ledger (append degree (append probe (append tensor (append scalar antisym)))) ∧
                Cont degree probe tensor ∧ Cont tensor antisym scalar := by
  intro degreeUnary probeUnary tensorRoute antisymUnary scalarRoute ledgerRoute
  have carrierRows :=
    DiffFormBHistCarrier_coordinate_ledger degreeUnary probeUnary tensorRoute antisymUnary
      scalarRoute ledgerRoute
  exact
    ⟨carrierRows.left,
      carrierRows.right.left,
      carrierRows.right.right.left,
      carrierRows.right.right.right.left,
      carrierRows.right.right.right.right,
      tensorRoute,
      scalarRoute⟩

theorem DiffFormRootWedgeProbe_obligation
    {leftDegree rightDegree outDegree leftLedger rightLedger tensorLedger : BHist}
    {left right : ProbeBundle BHist} :
    DiffFormWedgeProbeConcatenationLedger left right leftLedger rightLedger tensorLedger ->
      DiffFormWedgeDegreeLedger leftDegree rightDegree outDegree leftLedger rightLedger
          tensorLedger ->
        SemanticNameCert
            (fun row : BHist =>
              DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
                tensorLedger)
            (fun row : BHist =>
              DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
                tensorLedger)
            (fun row : BHist =>
              DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
                tensorLedger)
            hsame ∧
          hsame tensorLedger (append leftLedger rightLedger) ∧
            Cont leftDegree rightDegree outDegree ∧ UnaryHistory outDegree := by
  intro probeLedger degreeLedger
  have coverage := DiffFormWedgeProbeConcatenationLedger_coverage probeLedger
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
            tensorLedger)
        (fun row : BHist =>
          DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
            tensorLedger)
        (fun row : BHist =>
          DiffFormWedgeDegreeLedger leftDegree rightDegree row leftLedger rightLedger
            tensorLedger)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro outDegree degreeLedger
      · intro row _source
        exact hsame_refl row
      · intro row other same
        exact hsame_symm same
      · intro row other third leftSame rightSame
        exact hsame_trans leftSame rightSame
      · intro row other same source
        exact
          (DiffFormWedgeDegreeLedger_classifier_stability source (hsame_refl leftDegree)
            (hsame_refl rightDegree) same).left
    · intro _row source
      exact source
    · intro _row source
      exact source
  exact
    ⟨cert,
      coverage.right.right.right,
      degreeLedger.right.right.left,
      degreeLedger.right.right.right.left⟩

end BEDC.Derived.DiffFormUp
