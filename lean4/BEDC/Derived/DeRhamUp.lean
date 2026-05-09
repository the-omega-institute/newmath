import BEDC.FKernel.NameCert

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

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

end BEDC.Derived.DeRhamUp
