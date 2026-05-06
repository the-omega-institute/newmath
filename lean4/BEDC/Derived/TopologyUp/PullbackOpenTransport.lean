import BEDC.Derived.TopologyUp

namespace BEDC.Derived.TopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem BHistPullbackOpen_classifier_transport_surface (T : BHistIndexedOpenCarrier)
    {f : BHist -> BHist} {i : T.OpenIx} {U : BHist -> Prop}
    (mapUnary : forall {y : BHist}, UnaryHistory y -> UnaryHistory (f y))
    (mapSame :
      forall {y z : BHist}, UnaryHistory y -> UnaryHistory z -> hsame y z ->
        hsame (f y) (f z))
    (carries : BHistCarriesOpen T i U) :
    BHistPullbackCarriesOpen T f i U ∧
      (forall {y z : BHist}, UnaryHistory y -> UnaryHistory z -> hsame y z ->
        (BHistPullbackOpen f U y <-> BHistPullbackOpen f U z)) := by
  constructor
  · intro y unaryY unaryFY
    exact carries unaryFY
  · intro y z unaryY unaryZ sameYZ
    have unaryFY : UnaryHistory (f y) := mapUnary unaryY
    have unaryFZ : UnaryHistory (f z) := mapUnary unaryZ
    have sameF : hsame (f y) (f z) :=
      mapSame unaryY unaryZ sameYZ
    exact BHistCarriesOpen_classifier_transport T carries unaryFY unaryFZ sameF

end BEDC.Derived.TopologyUp
