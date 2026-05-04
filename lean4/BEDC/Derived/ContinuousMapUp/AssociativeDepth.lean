import BEDC.Derived.ContinuousMapUp

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.ContinuousUp
open BEDC.Derived.MetricUp

theorem ContinuousMapCarrier_associative_composition_depth_synchronization
    {source mid1 mid2 target mapF mapG mapH mapFG mapGH mapL mapR modF modG modH modFG
      modGH modL modR certF certG certH certFG certGH certL certR distF distG distH :
      BHist} :
    ContinuousMapCarrier source mapF mid1 modF certF distF ->
      ContinuousMapCarrier mid1 mapG mid2 modG certG distG ->
        ContinuousMapCarrier mid2 mapH target modH certH distH ->
          Cont mapF mapG mapFG -> Cont modF modG modFG -> Cont mid2 modFG certFG ->
            Cont mapFG mapH mapL -> Cont modFG modH modL -> Cont target modL certL ->
              Cont mapG mapH mapGH -> Cont modG modH modGH -> Cont target modGH certGH ->
                Cont mapF mapGH mapR -> Cont modF modGH modR -> Cont target modR certR ->
                  MetricDistanceDepth target =
                      MetricDistanceDepth source + MetricDistanceDepth mapL ∧
                    MetricDistanceDepth target =
                      MetricDistanceDepth source + MetricDistanceDepth mapR := by
  intro carrierF carrierG carrierH graphFG modulusFG certFGRel graphL modulusL certLRel
    graphGH modulusGH certGHRel graphR modulusR certRRel
  have carrierFG :
      ContinuousMapCarrier source mapFG mid2 modFG certFG (append source mid2) :=
    ContinuousMapCarrier_comp_closed carrierF carrierG graphFG modulusFG certFGRel
  have leftDepth :
      MetricDistanceDepth target = MetricDistanceDepth source + MetricDistanceDepth mapL :=
    ContinuousMap_comp_graph_depth_add carrierFG.left carrierH.left graphL modulusL certLRel
  have carrierGH :
      ContinuousMapCarrier mid1 mapGH target modGH certGH (append mid1 target) :=
    ContinuousMapCarrier_comp_closed carrierG carrierH graphGH modulusGH certGHRel
  have rightDepth :
      MetricDistanceDepth target = MetricDistanceDepth source + MetricDistanceDepth mapR :=
    ContinuousMap_comp_graph_depth_add carrierF.left carrierGH.left graphR modulusR certRRel
  exact And.intro leftDepth rightDepth

end BEDC.Derived.ContinuousMapUp
