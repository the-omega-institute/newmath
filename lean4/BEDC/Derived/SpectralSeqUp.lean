import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.SpectralSeqUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SpectralSeqBHistPageCarrier
    (abelian homology page differential readback convergence ledger provenance : BHist) : Prop :=
  UnaryHistory abelian ∧ UnaryHistory homology ∧ UnaryHistory page ∧
    UnaryHistory differential ∧ UnaryHistory readback ∧ UnaryHistory convergence ∧
      Cont page differential readback ∧ Cont readback convergence ledger ∧
        hsame provenance (append abelian homology)

theorem SpectralSeqBHistPageCarrier_successor_page_closure
    {abelian homology page differential readback convergence ledger provenance page' differential'
      readback' ledger' : BHist} :
    SpectralSeqBHistPageCarrier abelian homology page differential readback convergence ledger
        provenance ->
      hsame page page' ->
        hsame differential differential' ->
          Cont page' differential' readback' ->
            Cont readback' convergence ledger' ->
              SpectralSeqBHistPageCarrier abelian homology page' differential' readback'
                  convergence ledger' provenance ∧
                hsame readback readback' ∧ hsame ledger ledger' := by
  intro carrier samePage sameDifferential successorReadback successorLedger
  have pageUnary : UnaryHistory page' :=
    unary_transport carrier.right.right.left samePage
  have differentialUnary : UnaryHistory differential' :=
    unary_transport carrier.right.right.right.left sameDifferential
  have sameReadback : hsame readback readback' :=
    cont_respects_hsame samePage sameDifferential
      carrier.right.right.right.right.right.right.left successorReadback
  have readbackUnary : UnaryHistory readback' :=
    unary_transport carrier.right.right.right.right.left sameReadback
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameReadback (hsame_refl convergence)
      carrier.right.right.right.right.right.right.right.left successorLedger
  exact And.intro
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro pageUnary
          (And.intro differentialUnary
            (And.intro readbackUnary
              (And.intro carrier.right.right.right.right.right.left
                (And.intro successorReadback
                  (And.intro successorLedger
                    carrier.right.right.right.right.right.right.right.right))))))))
    (And.intro sameReadback sameLedger)

end BEDC.Derived.SpectralSeqUp
