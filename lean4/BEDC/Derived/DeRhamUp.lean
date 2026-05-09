import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

def DeRhamBoundarySourcePacket [AskSetup] [PackageSetup]
    (d : BHist -> BHist) (omega eta theta zero ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  DeRhamDoubleExteriorPacket d omega eta theta zero ∧ UnaryHistory theta ∧
    UnaryHistory ledger ∧ Cont theta ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem DeRhamBoundarySourcePacket_boundary_source_stability [AskSetup] [PackageSetup]
    {d : BHist -> BHist} {omega eta theta theta' zero ledger endpoint endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DeRhamBoundarySourcePacket d omega eta theta zero ledger endpoint bundle pkg ->
      hsame theta' theta ->
        Cont theta' ledger endpoint' ->
          PkgSig bundle endpoint' pkg ->
            DeRhamBoundarySourcePacket d omega eta theta' zero ledger endpoint' bundle pkg ∧
              UnaryHistory endpoint' ∧ hsame endpoint endpoint' ∧ DeRhamBoundary d theta' := by
  intro packet sameTheta endpointCont' pkgSig'
  have thetaUnary' : UnaryHistory theta' :=
    unary_transport packet.right.left (hsame_symm sameTheta)
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed thetaUnary' packet.right.right.left endpointCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame (hsame_symm sameTheta) (hsame_refl ledger)
      packet.right.right.right.left endpointCont'
  have doublePacket' : DeRhamDoubleExteriorPacket d omega eta theta' zero :=
    And.intro packet.left.left
      (And.intro (hsame_trans sameTheta packet.left.right.left)
        (And.intro packet.left.right.right.left
          (And.intro packet.left.right.right.right.left packet.left.right.right.right.right)))
  have boundary' : DeRhamBoundary d theta' :=
    (DeRhamDoubleExteriorPacket_boundary doublePacket').right.left
  have packet' :
      DeRhamBoundarySourcePacket d omega eta theta' zero ledger endpoint' bundle pkg :=
    And.intro doublePacket'
      (And.intro thetaUnary'
        (And.intro packet.right.right.left (And.intro endpointCont' pkgSig')))
  exact And.intro packet'
    (And.intro endpointUnary' (And.intro sameEndpoint boundary'))

end BEDC.Derived.DeRhamUp
