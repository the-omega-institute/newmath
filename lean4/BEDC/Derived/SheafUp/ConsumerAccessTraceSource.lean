import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive SheafConsumerAccessTraceSource (root : BHist) : Type where
  | carrierClassifier {sectionHist classifier : BHist} :
      UnaryHistory root -> UnaryHistory sectionHist -> hsame sectionHist classifier ->
        SheafConsumerAccessTraceSource root
  | restrictionRoute {openHist sectionHist result : BHist} :
      UnaryHistory root -> UnaryHistory openHist -> Cont openHist sectionHist result ->
        SheafConsumerAccessTraceSource root
  | coverMembership {member cover : BHist} :
      UnaryHistory root -> UnaryHistory member -> hsame member cover ->
        SheafConsumerAccessTraceSource root
  | localityGluing {common sectA sectB germA germB : BHist} :
      UnaryHistory root -> UnaryHistory common -> Cont common sectA germA ->
        Cont common sectB germB -> hsame germA germB -> SheafConsumerAccessTraceSource root

theorem SheafConsumerAccessTraceSource_root_unary {root : BHist} :
    SheafConsumerAccessTraceSource root -> UnaryHistory root := by
  intro source
  cases source with
  | carrierClassifier rootUnary _sectionUnary _sameSection =>
      exact rootUnary
  | restrictionRoute rootUnary _openUnary _route =>
      exact rootUnary
  | coverMembership rootUnary _memberUnary _sameMember =>
      exact rootUnary
  | localityGluing rootUnary _commonUnary _leftRoute _rightRoute _sameGerm =>
      exact rootUnary

end BEDC.Derived.SheafUp
