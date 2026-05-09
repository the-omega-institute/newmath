import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DeRhamDoubleExteriorDerivative_boundary {d : BHist -> BHist}
    {omega eta theta zero : BHist} :
    hsame eta (d omega) ->
      hsame theta (d eta) ->
        (forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) ->
          (forall a : BHist, hsame (d (d a)) zero) ->
            hsame zero BHist.Empty ->
              hsame theta zero ∧ (Exists (fun preimage : BHist => hsame theta (d preimage))) ∧
                hsame (d eta) BHist.Empty := by
  intro sameEta sameTheta dRespects squareZero zeroEmpty
  have sameDEta : hsame (d eta) (d (d omega)) :=
    dRespects sameEta
  have sameThetaZero : hsame theta zero :=
    hsame_trans sameTheta (hsame_trans sameDEta (squareZero omega))
  have sameDEtaEmpty : hsame (d eta) BHist.Empty :=
    hsame_trans (hsame_trans sameDEta (squareZero omega)) zeroEmpty
  exact And.intro sameThetaZero
    (And.intro (Exists.intro eta sameTheta) sameDEtaEmpty)
def DeRhamBoundary (d : BHist -> BHist) (b : BHist) : Prop :=
  exists a : BHist, hsame b (d a)

theorem DeRhamBoundary_zero_endpoint_hsame_transport
    {d : BHist -> BHist} {b b' zero : BHist} :
    DeRhamBoundary d b ->
      hsame b' b ->
        hsame b zero ->
          hsame zero BHist.Empty ->
            DeRhamBoundary d b' ∧ hsame b' BHist.Empty := by
  intro boundary sameB'B sameBZero sameZeroEmpty
  cases boundary with
  | intro preimage sameBPreimage =>
      have sameB'Preimage : hsame b' (d preimage) :=
        hsame_trans sameB'B sameBPreimage
      have sameB'Empty : hsame b' BHist.Empty :=
        hsame_trans sameB'B (hsame_trans sameBZero sameZeroEmpty)
      exact And.intro (Exists.intro preimage sameB'Preimage) sameB'Empty

theorem DeRhamBoundary_zero_endpoint_transport {d : BHist -> BHist} {b b' : BHist} :
    DeRhamBoundary d b -> hsame b' b -> hsame b BHist.Empty ->
      DeRhamBoundary d b' ∧ hsame b' BHist.Empty := by
  intro boundary sameBoundary sameZero
  cases boundary with
  | intro preimage samePreimage =>
      exact And.intro
        (Exists.intro preimage (hsame_trans sameBoundary samePreimage))
        (hsame_trans sameBoundary sameZero)

theorem DeRhamBoundary_hsame_transport_with_empty_endpoint
    {d : BHist -> BHist} {b b' : BHist} :
    DeRhamBoundary d b -> hsame b' b ->
      DeRhamBoundary d b' ∧ (hsame b BHist.Empty -> hsame b' BHist.Empty) := by
  intro boundary sameBoundary
  cases boundary with
  | intro preimage samePreimage =>
      exact And.intro
        (Exists.intro preimage (hsame_trans sameBoundary samePreimage))
        (fun sameEmpty => hsame_trans sameBoundary sameEmpty)

def DeRhamDoubleExteriorPacket
    (d : BHist -> BHist) (omega eta theta zero : BHist) : Prop :=
  hsame eta (d omega) ∧ hsame theta (d eta) ∧
    (forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) ∧
      (forall a : BHist, hsame (d (d a)) zero) ∧ hsame zero BHist.Empty

def DeRhamStandardBoundaryBridgePacket
    (d : BHist -> BHist) (omega eta theta zero provenance bridge : BHist) : Prop :=
  DeRhamDoubleExteriorPacket d omega eta theta zero ∧ Cont provenance theta bridge

def DeRhamBoundarySourceLedgerPacket
    (d : BHist -> BHist) (omega eta theta zero graphLedger endpointLedger : BHist) :
    Prop :=
  DeRhamDoubleExteriorPacket d omega eta theta zero ∧ DeRhamBoundary d theta ∧
    hsame (d eta) BHist.Empty ∧ Cont theta zero graphLedger ∧
      Cont graphLedger eta endpointLedger

theorem DeRhamDoubleExteriorPacket_boundary
    {d : BHist -> BHist} {omega eta theta zero : BHist} :
    DeRhamDoubleExteriorPacket d omega eta theta zero ->
      hsame theta zero ∧ DeRhamBoundary d theta ∧ hsame (d eta) BHist.Empty := by
  intro packet
  have sameDEtaDDOmega : hsame (d eta) (d (d omega)) :=
    packet.right.right.left packet.left
  have sameThetaDDOmega : hsame theta (d (d omega)) :=
    hsame_trans packet.right.left sameDEtaDDOmega
  have sameThetaZero : hsame theta zero :=
    hsame_trans sameThetaDDOmega (packet.right.right.right.left omega)
  have boundaryTheta : DeRhamBoundary d theta :=
    Exists.intro eta packet.right.left
  have sameDEtaZero : hsame (d eta) zero :=
    hsame_trans sameDEtaDDOmega (packet.right.right.right.left omega)
  exact And.intro sameThetaZero
    (And.intro boundaryTheta (hsame_trans sameDEtaZero packet.right.right.right.right))

inductive DeRhamStandardBoundaryGraphLedger (d : BHist -> BHist) :
    List BHist -> BHist -> Prop where
  | nil {endpoint : BHist} :
      hsame endpoint BHist.Empty -> DeRhamStandardBoundaryGraphLedger d [] endpoint
  | cons {omega eta theta zero tail endpoint : BHist} {rest : List BHist} :
      DeRhamDoubleExteriorPacket d omega eta theta zero ->
        DeRhamStandardBoundaryGraphLedger d rest tail -> Cont theta tail endpoint ->
          DeRhamStandardBoundaryGraphLedger d (theta :: rest) endpoint

theorem DeRhamStandardBoundaryGraphLedger_finite_graph_completeness
    {d : BHist -> BHist} {rows : List BHist} {endpoint row : BHist} :
    DeRhamStandardBoundaryGraphLedger d rows endpoint -> List.Mem row rows ->
      DeRhamBoundary d row ∧
        exists preimage : BHist, hsame row (d preimage) ∧
          hsame (d preimage) BHist.Empty := by
  intro ledger rowMem
  induction ledger with
  | nil _ =>
      cases rowMem
  | cons packet _ _ ih =>
      cases rowMem with
      | head =>
          have boundary := DeRhamDoubleExteriorPacket_boundary packet
          exact And.intro boundary.right.left
            (Exists.intro _ (And.intro packet.right.left boundary.right.right))
      | tail _ restMem =>
          exact ih restMem

theorem DeRhamStandardBoundaryGraphLedger_source_exhaustion
    {d : BHist -> BHist} {rows : List BHist} {endpoint : BHist} :
    DeRhamStandardBoundaryGraphLedger d rows endpoint ->
      (forall row : BHist, List.Mem row rows -> DeRhamBoundary d row) ∧
        (rows = [] -> hsame endpoint BHist.Empty) := by
  intro ledger
  induction ledger with
  | nil sameEndpoint =>
      exact And.intro
        (by
          intro row rowMem
          cases rowMem)
        (by
          intro _rowsEmpty
          exact sameEndpoint)
  | cons packet _ _ ih =>
      have headBoundary : DeRhamBoundary d _ :=
        (DeRhamDoubleExteriorPacket_boundary packet).right.left
      exact And.intro
        (by
          intro row rowMem
          cases rowMem with
          | head =>
              exact headBoundary
          | tail _ restMem =>
              exact ih.left row restMem)
        (by
          intro rowsEmpty
          cases rowsEmpty)

theorem DeRhamBoundary_packet_classifier_transport
    {d : BHist -> BHist} {omega eta theta zero theta' : BHist} :
    DeRhamDoubleExteriorPacket d omega eta theta zero ->
      hsame theta' theta ->
        DeRhamBoundary d theta' ∧ hsame theta' zero ∧ hsame (d eta) BHist.Empty := by
  intro packet sameTheta'
  have boundaryRows := DeRhamDoubleExteriorPacket_boundary packet
  have sameThetaEmpty : hsame theta BHist.Empty :=
    hsame_trans boundaryRows.left packet.right.right.right.right
  have transported :=
    DeRhamBoundary_zero_endpoint_transport boundaryRows.right.left sameTheta' sameThetaEmpty
  exact And.intro transported.left
    (And.intro (hsame_trans sameTheta' boundaryRows.left) boundaryRows.right.right)

theorem DeRhamBoundary_public_classifier_exactness
    {d : BHist -> BHist} {omega eta theta zero : BHist} :
    DeRhamDoubleExteriorPacket d omega eta theta zero ->
      SemanticNameCert (DeRhamBoundary d) (DeRhamBoundary d) (DeRhamBoundary d)
        (fun b c : BHist => DeRhamBoundary d b ∧ DeRhamBoundary d c ∧ hsame b c) ∧
        DeRhamBoundary d theta ∧ hsame (d eta) BHist.Empty := by
  intro packet
  have boundary := DeRhamDoubleExteriorPacket_boundary packet
  have boundaryTheta : DeRhamBoundary d theta := boundary.right.left
  have emptyDerivative : hsame (d eta) BHist.Empty := boundary.right.right
  have core :
      NameCert (DeRhamBoundary d)
        (fun b c : BHist => DeRhamBoundary d b ∧ DeRhamBoundary d c ∧ hsame b c) := {
    carrier_inhabited := Exists.intro theta boundaryTheta
    equiv_refl := by
      intro h boundaryH
      exact And.intro boundaryH (And.intro boundaryH (hsame_refl h))
    equiv_symm := by
      intro h k classified
      exact And.intro classified.right.left
        (And.intro classified.left (hsame_symm classified.right.right))
    equiv_trans := by
      intro h k r classifiedHK classifiedKR
      exact And.intro classifiedHK.left
        (And.intro classifiedKR.right.left
          (hsame_trans classifiedHK.right.right classifiedKR.right.right))
    carrier_respects_equiv := by
      intro h k classified _boundaryH
      exact classified.right.left
  }
  have cert :
      SemanticNameCert (DeRhamBoundary d) (DeRhamBoundary d) (DeRhamBoundary d)
        (fun b c : BHist => DeRhamBoundary d b ∧ DeRhamBoundary d c ∧ hsame b c) := {
    core := core
    pattern_sound := by
      intro h boundaryH
      exact boundaryH
    ledger_sound := by
      intro h boundaryH
      exact boundaryH
  }
  exact And.intro cert (And.intro boundaryTheta emptyDerivative)

theorem DeRhamStandardBoundaryBridgePacket_classifier_compatibility
    {d : BHist -> BHist} {omega eta theta zero provenance bridge : BHist} :
    DeRhamStandardBoundaryBridgePacket d omega eta theta zero provenance bridge ->
      DeRhamBoundary d theta ∧ hsame (d eta) BHist.Empty ∧ Cont provenance theta bridge := by
  intro packet
  have boundary := DeRhamDoubleExteriorPacket_boundary packet.left
  exact And.intro boundary.right.left (And.intro boundary.right.right packet.right)

theorem DeRhamStandardBoundaryBridgePacket_consumer_threshold
    {d : BHist -> BHist} {omega eta theta zero provenance bridge : BHist} :
    DeRhamStandardBoundaryBridgePacket d omega eta theta zero provenance bridge ->
      DeRhamBoundary d theta ∧ hsame theta zero ∧ hsame (d eta) BHist.Empty ∧
        (exists preimage : BHist, hsame theta (d preimage)) ∧
          Cont provenance theta bridge := by
  intro packet
  have boundary := DeRhamDoubleExteriorPacket_boundary packet.left
  exact And.intro boundary.right.left
    (And.intro boundary.left
      (And.intro boundary.right.right
        (And.intro boundary.right.left packet.right)))

theorem DeRhamStandardBoundaryBridgePacket_consumer_ledger_exhaustion
    {d : BHist -> BHist} {omega eta theta zero provenance bridge : BHist} :
    DeRhamStandardBoundaryBridgePacket d omega eta theta zero provenance bridge ->
      DeRhamBoundary d theta ∧ hsame theta zero ∧ hsame (d eta) BHist.Empty ∧
        hsame zero BHist.Empty ∧ Cont provenance theta bridge := by
  intro packet
  have boundary := DeRhamDoubleExteriorPacket_boundary packet.left
  exact And.intro boundary.right.left
    (And.intro boundary.left
      (And.intro boundary.right.right
        (And.intro packet.left.right.right.right.right packet.right)))

theorem DeRhamStandardBoundaryBridgePacket_boundary_preimage_threshold
    {d : BHist -> BHist} {omega eta theta zero provenance bridge : BHist} :
    DeRhamStandardBoundaryBridgePacket d omega eta theta zero provenance bridge ->
      (exists preimage : BHist, hsame theta (d preimage)) ∧ hsame theta zero ∧
        hsame (d eta) BHist.Empty ∧ Cont provenance theta bridge := by
  intro packet
  have boundary := DeRhamDoubleExteriorPacket_boundary packet.left
  exact And.intro boundary.right.left
    (And.intro boundary.left (And.intro boundary.right.right packet.right))

theorem DeRhamStandardBoundaryBridgePacket_classifier_transport
    {d : BHist -> BHist} {omega eta theta theta' zero provenance bridge bridge' : BHist} :
    DeRhamStandardBoundaryBridgePacket d omega eta theta zero provenance bridge ->
      hsame theta' theta ->
        Cont provenance theta' bridge' ->
          DeRhamBoundary d theta' ∧ hsame theta' zero ∧ hsame (d eta) BHist.Empty ∧
            hsame bridge bridge' := by
  intro packet sameTheta' bridgeRow'
  have boundary := DeRhamDoubleExteriorPacket_boundary packet.left
  cases boundary.right.left with
  | intro preimage sameThetaPreimage =>
      have boundaryTheta' : DeRhamBoundary d theta' :=
        Exists.intro preimage (hsame_trans sameTheta' sameThetaPreimage)
      have sameTheta'Zero : hsame theta' zero :=
        hsame_trans sameTheta' boundary.left
      have sameBridge : hsame bridge bridge' :=
        cont_respects_hsame (hsame_refl provenance) (hsame_symm sameTheta') packet.right
          bridgeRow'
      exact And.intro boundaryTheta'
        (And.intro sameTheta'Zero (And.intro boundary.right.right sameBridge))

theorem DeRhamBoundarySourceLedgerPacket_endpoint_transport
    {d : BHist -> BHist} {omega eta theta theta' zero graphLedger endpointLedger : BHist} :
    DeRhamBoundarySourceLedgerPacket d omega eta theta zero graphLedger endpointLedger ->
      hsame theta' theta ->
        DeRhamBoundary d theta' ∧ hsame (d eta) BHist.Empty ∧ hsame zero BHist.Empty ∧
          ∃ graphLedger' endpointLedger' : BHist,
            Cont theta' zero graphLedger' ∧ Cont graphLedger' eta endpointLedger' ∧
              hsame graphLedger graphLedger' ∧ hsame endpointLedger endpointLedger' := by
  intro packet sameTheta'
  cases packet with
  | intro doublePacket rest =>
      cases rest with
      | intro boundaryTheta rest =>
          cases rest with
          | intro sameDEtaEmpty rest =>
              cases rest with
              | intro graphCont endpointCont =>
                  cases boundaryTheta with
                  | intro preimage sameThetaPreimage =>
                      let graphLedger' := append theta' zero
                      let endpointLedger' := append graphLedger' eta
                      have boundaryTheta' : DeRhamBoundary d theta' :=
                        Exists.intro preimage (hsame_trans sameTheta' sameThetaPreimage)
                      have graphCont' : Cont theta' zero graphLedger' := by
                        rfl
                      have endpointCont' : Cont graphLedger' eta endpointLedger' := by
                        rfl
                      have sameGraphLedger : hsame graphLedger graphLedger' :=
                        cont_respects_hsame (hsame_symm sameTheta') (hsame_refl zero) graphCont
                          graphCont'
                      have sameEndpointLedger : hsame endpointLedger endpointLedger' :=
                        cont_respects_hsame sameGraphLedger (hsame_refl eta) endpointCont
                          endpointCont'
                      exact And.intro boundaryTheta'
                        (And.intro sameDEtaEmpty
                          (And.intro doublePacket.right.right.right.right
                            (Exists.intro graphLedger'
                              (Exists.intro endpointLedger'
                                (And.intro graphCont'
                                  (And.intro endpointCont'
                                    (And.intro sameGraphLedger sameEndpointLedger)))))))

theorem DeRhamBoundarySourceLedgerPacket_bridge_ledger_source_scope
    {d : BHist -> BHist} {omega eta theta zero graphLedger endpointLedger : BHist} :
    DeRhamBoundarySourceLedgerPacket d omega eta theta zero graphLedger endpointLedger ->
      DeRhamBoundary d theta ∧ hsame zero BHist.Empty ∧ hsame (d eta) BHist.Empty ∧
        Cont theta zero graphLedger ∧ Cont graphLedger eta endpointLedger := by
  intro packet
  exact And.intro packet.right.left
    (And.intro packet.left.right.right.right.right
      (And.intro packet.right.right.left
        (And.intro packet.right.right.right.left packet.right.right.right.right)))

theorem DeRhamRootUnblock_threshold_surface
    {d : BHist -> BHist} {omega eta theta theta' zero graphLedger endpointLedger : BHist} :
    DeRhamBoundarySourceLedgerPacket d omega eta theta zero graphLedger endpointLedger ->
      hsame theta' theta ->
        DeRhamBoundary d theta ∧ DeRhamBoundary d theta' ∧ hsame zero BHist.Empty ∧
          hsame (d eta) BHist.Empty ∧
            ∃ graphLedger' endpointLedger' : BHist,
              Cont theta' zero graphLedger' ∧ Cont graphLedger' eta endpointLedger' ∧
                hsame graphLedger graphLedger' ∧ hsame endpointLedger endpointLedger' := by
  intro packet sameTheta'
  have sourceRows :=
    DeRhamBoundarySourceLedgerPacket_bridge_ledger_source_scope packet
  have endpointRows :=
    DeRhamBoundarySourceLedgerPacket_endpoint_transport packet sameTheta'
  exact And.intro sourceRows.left
    (And.intro endpointRows.left
      (And.intro sourceRows.right.left
        (And.intro sourceRows.right.right.left endpointRows.right.right.right)))

theorem DeRhamBoundary_semanticNameCert {d : BHist -> BHist} {axis : BHist}
    (axisBoundary : DeRhamBoundary d axis) :
    SemanticNameCert (DeRhamBoundary d) (DeRhamBoundary d) (DeRhamBoundary d) hsame := by
  exact {
    core := {
      carrier_inhabited := Exists.intro axis axisBoundary
      equiv_refl := by
        intro h _boundary
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k same boundaryH
        cases boundaryH with
        | intro preimage sameH =>
            exact Exists.intro preimage (hsame_trans (hsame_symm same) sameH)
    }
    pattern_sound := by
      intro _h boundary
      exact boundary
    ledger_sound := by
      intro _h boundary
      exact boundary
  }

def DeRhamBoundarySourcePacket (d : BHist -> BHist) (theta zero : BHist) : Prop :=
  DeRhamBoundary d theta ∧ hsame zero BHist.Empty

theorem DeRhamBoundarySourcePacket_stability
    {d : BHist -> BHist} {theta theta' zero : BHist} :
    DeRhamBoundarySourcePacket d theta zero ->
      hsame theta' theta ->
        DeRhamBoundarySourcePacket d theta' zero ∧ DeRhamBoundary d theta' ∧
          hsame zero BHist.Empty := by
  intro packet sameTheta
  cases packet with
  | intro boundary zeroEmpty =>
      cases boundary with
      | intro preimage boundaryTheta =>
          have boundaryTheta' : DeRhamBoundary d theta' :=
            Exists.intro preimage (hsame_trans sameTheta boundaryTheta)
          exact And.intro (And.intro boundaryTheta' zeroEmpty)
            (And.intro boundaryTheta' zeroEmpty)

theorem DeRhamBoundarySourceLedgerPacket_consumer_exactness
    {d : BHist -> BHist} {omega eta theta zero graphLedger endpointLedger : BHist} :
    DeRhamBoundarySourceLedgerPacket d omega eta theta zero graphLedger endpointLedger ->
      hsame theta zero ∧ DeRhamBoundary d theta ∧ hsame (d eta) BHist.Empty ∧
        Cont theta zero graphLedger ∧ Cont graphLedger eta endpointLedger := by
  intro packet
  have boundary := DeRhamDoubleExteriorPacket_boundary packet.left
  exact And.intro boundary.left
    (And.intro boundary.right.left
      (And.intro boundary.right.right
        (And.intro packet.right.right.right.left packet.right.right.right.right)))

theorem DeRhamBoundarySourcePacket_consumer_exactness
    {d : BHist -> BHist} {omega eta theta theta' zero : BHist} :
    DeRhamDoubleExteriorPacket d omega eta theta zero ->
      hsame theta' theta ->
        DeRhamBoundarySourcePacket d theta' zero ∧ DeRhamBoundary d theta' ∧
          hsame theta' zero ∧ hsame (d eta) BHist.Empty ∧ hsame zero BHist.Empty := by
  intro packet sameTheta'
  have boundaryRows := DeRhamDoubleExteriorPacket_boundary packet
  have boundaryTheta' : DeRhamBoundary d theta' := by
    cases boundaryRows.right.left with
    | intro preimage sameThetaPreimage =>
        exact Exists.intro preimage (hsame_trans sameTheta' sameThetaPreimage)
  have theta'Zero : hsame theta' zero :=
    hsame_trans sameTheta' boundaryRows.left
  have zeroEmpty : hsame zero BHist.Empty :=
    packet.right.right.right.right
  exact And.intro (And.intro boundaryTheta' zeroEmpty)
    (And.intro boundaryTheta'
      (And.intro theta'Zero
        (And.intro boundaryRows.right.right zeroEmpty)))

end BEDC.Derived.DeRhamUp
