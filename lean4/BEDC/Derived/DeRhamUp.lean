import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

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

def DeRhamDoubleExteriorPacket
    (d : BHist -> BHist) (omega eta theta zero : BHist) : Prop :=
  hsame eta (d omega) ∧ hsame theta (d eta) ∧
    (forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) ∧
      (forall a : BHist, hsame (d (d a)) zero) ∧ hsame zero BHist.Empty

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

end BEDC.Derived.DeRhamUp
