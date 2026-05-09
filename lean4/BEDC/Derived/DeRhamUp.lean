import BEDC.FKernel.Hist

namespace BEDC.Derived.DeRhamUp

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

theorem DeRhamBoundary_zero_endpoint_transport {d : BHist -> BHist} {b b' : BHist} :
    DeRhamBoundary d b -> hsame b' b -> hsame b BHist.Empty ->
      DeRhamBoundary d b' ∧ hsame b' BHist.Empty := by
  intro boundary sameBoundary sameZero
  cases boundary with
  | intro preimage samePreimage =>
      exact And.intro
        (Exists.intro preimage (hsame_trans sameBoundary samePreimage))
        (hsame_trans sameBoundary sameZero)

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

end BEDC.Derived.DeRhamUp
