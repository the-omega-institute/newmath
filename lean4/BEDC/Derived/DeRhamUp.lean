import BEDC.FKernel.Hist

namespace BEDC.Derived.DeRhamUp

open BEDC.FKernel.Hist

theorem DeRhamExteriorSquareZero_boundary_cocycle {d : BHist -> BHist}
    {omega eta theta z : BHist} :
    hsame eta (d omega) ->
      hsame theta (d eta) ->
        (forall {a b : BHist}, hsame a b -> hsame (d a) (d b)) ->
          (forall a : BHist, hsame (d (d a)) z) ->
            hsame z BHist.Empty ->
              hsame theta z ∧ (exists a : BHist, hsame theta (d a)) ∧
                hsame (d eta) BHist.Empty := by
  intro etaGraph thetaGraph dCongr squareZero zEmpty
  have dEtaToDDOmega : hsame (d eta) (d (d omega)) :=
    dCongr etaGraph
  have dEtaToZ : hsame (d eta) z :=
    hsame_trans dEtaToDDOmega (squareZero omega)
  have thetaToZ : hsame theta z :=
    hsame_trans thetaGraph dEtaToZ
  have boundaryWitness : exists a : BHist, hsame theta (d a) :=
    Exists.intro eta thetaGraph
  have dEtaEmpty : hsame (d eta) BHist.Empty :=
    hsame_trans dEtaToZ zEmpty
  exact And.intro thetaToZ (And.intro boundaryWitness dEtaEmpty)

end BEDC.Derived.DeRhamUp
