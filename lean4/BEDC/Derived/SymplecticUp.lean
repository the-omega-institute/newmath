import BEDC.Derived.DiffFormUp
import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SymplecticUp

open BEDC.Derived.DiffFormUp
open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SymplecticCarrierClassifierSurface
    (manifold form derivative degree degreePlus probe probe' tensor tensor' scalar scalar'
      antisym source closedWitness pairing ledger : BHist) : Prop :=
  ManifoldSingletonCarrier manifold ∧
    DiffFormExteriorDerivativeLedger form derivative degree degreePlus probe probe' tensor
      tensor' scalar scalar' antisym source ∧
      hsame derivative BHist.Empty ∧ Cont form pairing ledger ∧ hsame closedWitness derivative

theorem SymplecticCarrierClassifierSurface_carrier_classifier_obligations
    {manifold form derivative degree degreePlus probe probe' tensor tensor' scalar scalar'
      antisym source closedWitness pairing ledger : BHist} :
    SymplecticCarrierClassifierSurface manifold form derivative degree degreePlus probe probe'
      tensor tensor' scalar scalar' antisym source closedWitness pairing ledger ->
      ManifoldSingletonCarrier manifold ∧ UnaryHistory manifold ∧ UnaryHistory form ∧
        UnaryHistory derivative ∧ UnaryHistory degree ∧ UnaryHistory degreePlus ∧
          Cont degree (BHist.e1 BHist.Empty) degreePlus ∧ hsame closedWitness BHist.Empty := by
  intro surface
  have manifoldRows := ManifoldSingletonCarrier_topology_scope surface.left
  have degreeRows := DiffFormExteriorDerivativeLedger_degree_raise surface.right.left
  have closedEmpty : hsame closedWitness BHist.Empty :=
    hsame_trans surface.right.right.right.right surface.right.right.left
  exact And.intro surface.left
    (And.intro manifoldRows.right.left
      (And.intro surface.right.left.left
        (And.intro surface.right.left.right.left
          (And.intro degreeRows.left
            (And.intro degreeRows.right.left
              (And.intro degreeRows.right.right closedEmpty))))))

def SymplecticCarrierClassifierEndpointSurface
    (manifold form derivative closed pairing : BHist) : Prop :=
  ManifoldSingletonCarrier manifold ∧ UnaryHistory form ∧ UnaryHistory derivative ∧
    Cont form derivative closed ∧ Cont manifold form pairing

theorem SymplecticCarrierClassifierEndpointSurface_obligations
    {manifold form derivative closed pairing : BHist} :
    SymplecticCarrierClassifierEndpointSurface manifold form derivative closed pairing ->
      ManifoldSingletonCarrier manifold ∧ UnaryHistory manifold ∧ UnaryHistory form ∧
        UnaryHistory derivative ∧ UnaryHistory closed ∧ UnaryHistory pairing ∧
          Cont form derivative closed ∧ Cont manifold form pairing := by
  intro surface
  have manifoldRows := ManifoldSingletonCarrier_topology_scope surface.left
  have closedUnary : UnaryHistory closed :=
    unary_cont_closed surface.right.left surface.right.right.left surface.right.right.right.left
  have pairingUnary : UnaryHistory pairing :=
    unary_cont_closed manifoldRows.right.left surface.right.left surface.right.right.right.right
  have formUnary : UnaryHistory form := surface.right.left
  have derivativeUnary : UnaryHistory derivative := surface.right.right.left
  have closedRow : Cont form derivative closed := surface.right.right.right.left
  have pairingRow : Cont manifold form pairing := surface.right.right.right.right
  exact And.intro surface.left
    (And.intro manifoldRows.right.left
      (And.intro formUnary
        (And.intro derivativeUnary
          (And.intro closedUnary
            (And.intro pairingUnary
              (And.intro closedRow pairingRow))))))

theorem SymplecticCarrierClassifierSurface_obligations
    {manifold form derivative degree degreePlus probe probe' tensor tensor' scalar scalar'
      antisym source closedWitness pairing ledger : BHist} :
    SymplecticCarrierClassifierSurface manifold form derivative degree degreePlus probe probe'
      tensor tensor' scalar scalar' antisym source closedWitness pairing ledger ->
      ManifoldSingletonCarrier manifold ∧ UnaryHistory manifold ∧ UnaryHistory form ∧
        UnaryHistory derivative ∧ UnaryHistory degree ∧ UnaryHistory degreePlus ∧
          Cont degree (BHist.e1 BHist.Empty) degreePlus ∧ hsame closedWitness BHist.Empty := by
  intro surface
  exact SymplecticCarrierClassifierSurface_carrier_classifier_obligations surface

theorem SymplecticCarrierClassifierSurface_closed_two_form_obligation
    {manifold form derivative degree degreePlus probe probe' tensor tensor' scalar scalar'
      antisym source closedWitness pairing ledger : BHist} :
    SymplecticCarrierClassifierSurface manifold form derivative degree degreePlus probe probe'
      tensor tensor' scalar scalar' antisym source closedWitness pairing ledger ->
      hsame derivative BHist.Empty ∧ hsame closedWitness BHist.Empty ∧
        UnaryHistory derivative ∧ UnaryHistory closedWitness ∧ Cont form pairing ledger := by
  intro surface
  have obligations :=
    SymplecticCarrierClassifierSurface_carrier_classifier_obligations surface
  have closedUnary : UnaryHistory closedWitness :=
    unary_transport_symm obligations.right.right.right.left surface.right.right.right.right
  exact And.intro surface.right.right.left
    (And.intro obligations.right.right.right.right.right.right.right
      (And.intro obligations.right.right.right.left
        (And.intro closedUnary surface.right.right.right.left)))

def SymplecticObligationBoundary
    (manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness : BHist) : Prop :=
  ManifoldSingletonCarrier manifold ∧
    DiffFormExteriorDerivativeLedger scalar derivative degree raised probe probe tensor tensor
      scalar scalar antisym ledger ∧
    hsame degree (BHist.e1 (BHist.e1 BHist.Empty)) ∧
    Cont raised BHist.Empty closedWitness ∧ Cont manifold scalar nondegWitness

theorem SymplecticObligationBoundary_carrier_classifier_obligations
    {manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness : BHist} :
    SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger derivative
      raised closedWitness nondegWitness ->
      ManifoldSingletonCarrier manifold ∧
        DiffFormExteriorDerivativeLedger scalar derivative degree raised probe probe tensor tensor
          scalar scalar antisym ledger ∧
        hsame degree (BHist.e1 (BHist.e1 BHist.Empty)) ∧
        UnaryHistory manifold ∧ UnaryHistory raised ∧ UnaryHistory closedWitness ∧
          UnaryHistory nondegWitness := by
  intro boundary
  have manifoldRows := ManifoldSingletonCarrier_topology_scope boundary.left
  have degreeRows :=
    DiffFormExteriorDerivativeLedger_degree_raise boundary.right.left
  have closedUnary : UnaryHistory closedWitness :=
    unary_cont_closed degreeRows.right.left unary_empty boundary.right.right.right.left
  have nondegUnary : UnaryHistory nondegWitness :=
    unary_cont_closed manifoldRows.right.left boundary.right.left.left
      boundary.right.right.right.right
  exact And.intro boundary.left
    (And.intro boundary.right.left
      (And.intro boundary.right.right.left
        (And.intro manifoldRows.right.left
          (And.intro degreeRows.right.left
            (And.intro closedUnary nondegUnary)))))

theorem SymplecticObligationBoundary_closed_two_form_transport
    {manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness scalar' derivative' raised' closedWitness' : BHist} :
    SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger derivative
        raised closedWitness nondegWitness ->
      hsame scalar scalar' -> hsame derivative derivative' -> hsame raised raised' ->
        Cont raised' BHist.Empty closedWitness' ->
          SymplecticObligationBoundary manifold degree probe tensor scalar' antisym ledger
              derivative' raised' closedWitness' nondegWitness ∧
            hsame closedWitness closedWitness' := by
  intro boundary sameScalar sameDerivative sameRaised closedRow'
  have ledger' :
      DiffFormExteriorDerivativeLedger scalar' derivative' degree raised' probe probe tensor tensor
        scalar' scalar' antisym ledger ∧
        UnaryHistory degree ∧ UnaryHistory raised' ∧
          Cont degree (BHist.e1 BHist.Empty) raised' :=
    DiffFormExteriorDerivativeLedger_hsame_transport_degree_raise
      sameScalar sameDerivative (hsame_refl degree) sameRaised (hsame_refl probe)
      (hsame_refl probe) (hsame_refl tensor) (hsame_refl tensor) sameScalar sameScalar
      (hsame_refl antisym) (hsame_refl ledger) boundary.right.left
  have sameClosed : hsame closedWitness closedWitness' :=
    cont_respects_hsame sameRaised (hsame_refl BHist.Empty) boundary.right.right.right.left
      closedRow'
  have nondegRow' : Cont manifold scalar' nondegWitness :=
    cont_hsame_transport (hsame_refl manifold) sameScalar (hsame_refl nondegWitness)
      boundary.right.right.right.right
  exact And.intro
    (And.intro boundary.left
      (And.intro ledger'.left
        (And.intro boundary.right.right.left
          (And.intro closedRow' nondegRow'))))
    sameClosed

theorem SymplecticObligationBoundary_nondegeneracy_transport
    {manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness scalar' nondegWitness' : BHist} :
    SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger derivative
        raised closedWitness nondegWitness ->
      hsame scalar scalar' -> Cont manifold scalar' nondegWitness' ->
        SymplecticObligationBoundary manifold degree probe tensor scalar' antisym ledger
            derivative raised closedWitness nondegWitness' ∧
          hsame nondegWitness nondegWitness' := by
  intro boundary sameScalar nondegRow'
  have ledger' :
      DiffFormExteriorDerivativeLedger scalar' derivative degree raised probe probe tensor tensor
        scalar' scalar' antisym ledger ∧
        UnaryHistory degree ∧ UnaryHistory raised ∧
          Cont degree (BHist.e1 BHist.Empty) raised :=
    DiffFormExteriorDerivativeLedger_hsame_transport_degree_raise
      sameScalar (hsame_refl derivative) (hsame_refl degree) (hsame_refl raised)
      (hsame_refl probe) (hsame_refl probe) (hsame_refl tensor) (hsame_refl tensor)
      sameScalar sameScalar (hsame_refl antisym) (hsame_refl ledger) boundary.right.left
  have sameNondeg : hsame nondegWitness nondegWitness' :=
    cont_respects_hsame (hsame_refl manifold) sameScalar boundary.right.right.right.right
      nondegRow'
  exact And.intro
    (And.intro boundary.left
      (And.intro ledger'.left
        (And.intro boundary.right.right.left
          (And.intro boundary.right.right.right.left nondegRow'))))
    sameNondeg

theorem SymplecticObligationBoundary_closed_nondegenerate_public_stability
    {manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness scalar' derivative' raised' closedWitness' nondegWitness' : BHist} :
    SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger derivative
        raised closedWitness nondegWitness ->
      hsame scalar scalar' -> hsame derivative derivative' -> hsame raised raised' ->
        Cont raised' BHist.Empty closedWitness' ->
          Cont manifold scalar' nondegWitness' ->
            SymplecticObligationBoundary manifold degree probe tensor scalar' antisym ledger
                derivative' raised' closedWitness' nondegWitness' ∧
              hsame closedWitness closedWitness' ∧
                hsame nondegWitness nondegWitness' := by
  intro boundary sameScalar sameDerivative sameRaised closedRow' nondegRow'
  have closedTransport :=
    SymplecticObligationBoundary_closed_two_form_transport boundary sameScalar sameDerivative
      sameRaised closedRow'
  have nondegTransport :=
    SymplecticObligationBoundary_nondegeneracy_transport closedTransport.left
      (hsame_refl scalar') nondegRow'
  exact And.intro nondegTransport.left
    (And.intro closedTransport.right nondegTransport.right)

end BEDC.Derived.SymplecticUp
