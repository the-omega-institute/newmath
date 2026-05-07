import BEDC.Derived.DiffFormUp
import BEDC.Derived.ManifoldUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SymplecticUp

open BEDC.Derived.DiffFormUp
open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem SymplecticCarrierClassifierSurface_closed_two_form_transport
    {manifold form derivative degree degreePlus probe probe' tensor tensor' scalar scalar'
      antisym source closedWitness pairing ledger derivative' closedWitness' : BHist} :
    SymplecticCarrierClassifierSurface manifold form derivative degree degreePlus probe probe'
      tensor tensor' scalar scalar' antisym source closedWitness pairing ledger ->
      hsame derivative derivative' -> hsame closedWitness closedWitness' ->
        hsame derivative' BHist.Empty ∧ hsame closedWitness' BHist.Empty ∧
          UnaryHistory derivative' := by
  intro surface sameDerivative sameClosedWitness
  have derivativeEmpty : hsame derivative' BHist.Empty :=
    hsame_trans (hsame_symm sameDerivative) surface.right.right.left
  have closedWitnessEmpty : hsame closedWitness BHist.Empty :=
    hsame_trans surface.right.right.right.right surface.right.right.left
  have transportedClosedWitnessEmpty : hsame closedWitness' BHist.Empty :=
    hsame_trans (hsame_symm sameClosedWitness) closedWitnessEmpty
  have derivativeUnary : UnaryHistory derivative' :=
    unary_transport surface.right.left.right.left sameDerivative
  exact And.intro derivativeEmpty
    (And.intro transportedClosedWitnessEmpty derivativeUnary)

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

theorem SymplecticCarrierClassifierEndpointSurface_closed_two_form_transport
    {manifold form derivative closed pairing closed' : BHist} :
    SymplecticCarrierClassifierEndpointSurface manifold form derivative closed pairing ->
      hsame closed closed' -> Cont form derivative closed' ->
        SymplecticCarrierClassifierEndpointSurface manifold form derivative closed' pairing ∧
          hsame closed closed' ∧ UnaryHistory closed' := by
  intro surface sameClosed transportedClosed
  have closedUnary : UnaryHistory closed' :=
    unary_cont_closed surface.right.left surface.right.right.left transportedClosed
  exact And.intro
    (And.intro surface.left
      (And.intro surface.right.left
        (And.intro surface.right.right.left
          (And.intro transportedClosed surface.right.right.right.right))))
    (And.intro sameClosed closedUnary)

theorem SymplecticCarrierClassifierEndpointSurface_nondegeneracy_transport
    {manifold form derivative closed pairing form' pairing' : BHist} :
    SymplecticCarrierClassifierEndpointSurface manifold form derivative closed pairing ->
      hsame form form' -> Cont manifold form' pairing' ->
        SymplecticCarrierClassifierEndpointSurface manifold form' derivative closed pairing' ∧
          hsame pairing pairing' ∧ UnaryHistory pairing' := by
  intro surface sameForm pairingRow'
  have closedRow' : Cont form' derivative closed :=
    cont_hsame_transport sameForm (hsame_refl derivative) (hsame_refl closed)
      surface.right.right.right.left
  have pairingSame : hsame pairing pairing' :=
    cont_respects_hsame (hsame_refl manifold) sameForm surface.right.right.right.right
      pairingRow'
  have formUnary' : UnaryHistory form' :=
    unary_transport surface.right.left sameForm
  have manifoldRows := ManifoldSingletonCarrier_topology_scope surface.left
  have pairingUnary' : UnaryHistory pairing' :=
    unary_cont_closed manifoldRows.right.left formUnary' pairingRow'
  exact And.intro
    (And.intro surface.left
      (And.intro formUnary'
        (And.intro surface.right.right.left
          (And.intro closedRow' pairingRow'))))
    (And.intro pairingSame pairingUnary')

theorem SymplecticCarrierClassifierEndpointSurface_semantic_name_certificate
    {manifold form derivative closed pairing : BHist} :
    SymplecticCarrierClassifierEndpointSurface manifold form derivative closed pairing ->
      SemanticNameCert
        (fun endpoint : BHist =>
          ∃ carriedForm carriedClosed : BHist,
            SymplecticCarrierClassifierEndpointSurface manifold carriedForm derivative
              carriedClosed endpoint)
        (fun endpoint : BHist =>
          ∃ carriedForm carriedClosed : BHist,
            SymplecticCarrierClassifierEndpointSurface manifold carriedForm derivative
              carriedClosed endpoint)
        (fun endpoint : BHist =>
          ∃ carriedForm carriedClosed : BHist,
            SymplecticCarrierClassifierEndpointSurface manifold carriedForm derivative
              carriedClosed endpoint)
        (fun left right : BHist =>
          (∃ carriedForm carriedClosed : BHist,
            SymplecticCarrierClassifierEndpointSurface manifold carriedForm derivative
              carriedClosed left) ∧
          (∃ carriedForm carriedClosed : BHist,
            SymplecticCarrierClassifierEndpointSurface manifold carriedForm derivative
              carriedClosed right) ∧
          hsame left right) := by
  intro surface
  constructor
  · constructor
    · exact Exists.intro pairing (Exists.intro form (Exists.intro closed surface))
    · intro endpoint carrier
      exact And.intro carrier (And.intro carrier (hsame_refl endpoint))
    · intro endpoint endpoint' classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    · intro endpoint endpoint' endpoint'' classifiedLeft classifiedRight
      exact And.intro classifiedLeft.left
        (And.intro classifiedRight.right.left
          (hsame_trans classifiedLeft.right.right classifiedRight.right.right))
    · intro endpoint endpoint' classified _carrier
      exact classified.right.left
  · intro _endpoint source
    exact source
  · intro _endpoint source
    exact source

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

theorem SymplecticObligationBoundary_ledger_exactness_obligation
    {manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness : BHist} :
    SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger derivative
      raised closedWitness nondegWitness ->
      ManifoldSingletonCarrier manifold ∧
        DiffFormExteriorDerivativeLedger scalar derivative degree raised probe probe tensor tensor
          scalar scalar antisym ledger ∧
        hsame degree (BHist.e1 (BHist.e1 BHist.Empty)) ∧
        Cont raised BHist.Empty closedWitness ∧
        Cont manifold scalar nondegWitness ∧
        UnaryHistory closedWitness ∧ UnaryHistory nondegWitness := by
  intro boundary
  have obligations := SymplecticObligationBoundary_carrier_classifier_obligations boundary
  exact And.intro obligations.left
    (And.intro obligations.right.left
      (And.intro obligations.right.right.left
        (And.intro boundary.right.right.right.left
          (And.intro boundary.right.right.right.right
            (And.intro obligations.right.right.right.right.right.left
              obligations.right.right.right.right.right.right)))))

theorem SymplecticObligationBoundary_closed_two_form_row
    {manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness : BHist} :
    SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger derivative
        raised closedWitness nondegWitness ->
      Cont raised BHist.Empty closedWitness ∧ hsame closedWitness raised ∧
        UnaryHistory closedWitness := by
  intro boundary
  have obligations := SymplecticObligationBoundary_carrier_classifier_obligations boundary
  have closedRow : Cont raised BHist.Empty closedWitness := boundary.right.right.right.left
  exact And.intro closedRow
    (And.intro (cont_right_unit_result closedRow)
      obligations.right.right.right.right.right.left)

theorem SymplecticObligationBoundary_nondegeneracy_row
    {manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness : BHist} :
    SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger derivative
        raised closedWitness nondegWitness ->
      Cont manifold scalar nondegWitness ∧ ManifoldSingletonCarrier manifold ∧
        UnaryHistory manifold ∧ UnaryHistory nondegWitness := by
  intro boundary
  have obligations := SymplecticObligationBoundary_carrier_classifier_obligations boundary
  exact And.intro boundary.right.right.right.right
    (And.intro obligations.left
      (And.intro obligations.right.right.right.left
        obligations.right.right.right.right.right.right))

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

theorem SymplecticObligationBoundary_semantic_name_certificate
    {manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness : BHist} :
    SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger derivative
        raised closedWitness nondegWitness ->
      SemanticNameCert
        (fun endpoint : BHist =>
          SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger
            derivative raised closedWitness endpoint)
        (fun endpoint : BHist =>
          SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger
            derivative raised closedWitness endpoint)
        (fun endpoint : BHist =>
          SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger
            derivative raised closedWitness endpoint)
        hsame := by
  intro boundary
  exact {
    core := {
      carrier_inhabited := Exists.intro nondegWitness boundary
      equiv_refl := by
        intro endpoint _source
        exact hsame_refl endpoint
      equiv_symm := by
        intro _endpoint _endpoint' sameEndpoint
        exact hsame_symm sameEndpoint
      equiv_trans := by
        intro _endpoint _endpoint' _endpoint'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro endpoint endpoint' sameEndpoint source
        exact And.intro source.left
          (And.intro source.right.left
            (And.intro source.right.right.left
              (And.intro source.right.right.right.left
                (cont_hsame_transport (hsame_refl manifold) (hsame_refl scalar) sameEndpoint
                  source.right.right.right.right))))
    }
    pattern_sound := by
      intro _endpoint source
      exact source
    ledger_sound := by
      intro _endpoint source
      exact source
  }

theorem SymplecticObligationBoundary_nondegeneracy_endpoint_split
    {manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness : BHist} :
    SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger derivative
      raised closedWitness nondegWitness ->
      hsame nondegWitness BHist.Empty ->
        hsame manifold BHist.Empty ∧ hsame scalar BHist.Empty ∧ UnaryHistory scalar ∧
          UnaryHistory nondegWitness := by
  intro boundary nondegEmpty
  have manifoldRows := ManifoldSingletonCarrier_topology_scope boundary.left
  have endpointToEmpty : Cont manifold scalar BHist.Empty :=
    cont_result_hsame_transport boundary.right.right.right.right nondegEmpty
  have endpointParts := cont_empty_result_inversion endpointToEmpty
  have scalarUnary : UnaryHistory scalar := boundary.right.left.left
  have nondegUnary : UnaryHistory nondegWitness :=
    unary_cont_closed manifoldRows.right.left scalarUnary boundary.right.right.right.right
  exact And.intro manifoldRows.left
    (And.intro endpointParts.right (And.intro scalarUnary nondegUnary))

theorem SymplecticObligationBoundary_closed_successor_not_empty
    {manifold degree probe tensor scalar antisym ledger derivative raised closedWitness
      nondegWitness : BHist} :
    SymplecticObligationBoundary manifold degree probe tensor scalar antisym ledger derivative
      raised closedWitness nondegWitness ->
      hsame closedWitness BHist.Empty -> False := by
  intro boundary closedEmpty
  have successorRows :=
    DiffFormExteriorDerivativeLedger_degree_successor_nonempty boundary.right.left
  have closedRaised : hsame closedWitness raised :=
    cont_right_unit_result boundary.right.right.right.left
  have raisedEmpty : hsame raised BHist.Empty :=
    hsame_trans (hsame_symm closedRaised) closedEmpty
  exact successorRows.right.right.right raisedEmpty

end BEDC.Derived.SymplecticUp
