import BEDC.Derived.BanachSpaceUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def BanachSpaceCompleteMetricReduction (V N M Q S R E Z : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory V ∧ UnaryHistory N ∧ UnaryHistory M ∧ UnaryHistory Q ∧ UnaryHistory S ∧
    UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory Z ∧
      ∃ normMetric cauchyRead completionRead toleranceRead separatedRead : BHist,
        Cont V N normMetric ∧ Cont Q S cauchyRead ∧
          Cont cauchyRead R completionRead ∧ Cont completionRead E toleranceRead ∧
            Cont toleranceRead Z separatedRead

theorem BanachSpaceCompleteMetricReduction_surface
    {V N M Q S R E Z normMetric cauchyRead completionRead toleranceRead
      separatedRead : BHist} :
    UnaryHistory V →
      UnaryHistory N →
        UnaryHistory M →
          UnaryHistory Q →
            UnaryHistory S →
              UnaryHistory R →
                UnaryHistory E →
                  UnaryHistory Z →
                    Cont V N normMetric →
                      Cont Q S cauchyRead →
                        Cont cauchyRead R completionRead →
                          Cont completionRead E toleranceRead →
                            Cont toleranceRead Z separatedRead →
                              BanachSpaceCompleteMetricReduction V N M Q S R E Z ∧
                                UnaryHistory normMetric ∧ UnaryHistory cauchyRead ∧
                                  UnaryHistory completionRead ∧ UnaryHistory toleranceRead ∧
                                    UnaryHistory separatedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory BanachSpaceCompleteMetricReduction
  intro vUnary nUnary mUnary qUnary sUnary rUnary eUnary zUnary normRoute cauchyRoute
    completionRoute toleranceRoute separatedRoute
  have normUnary : UnaryHistory normMetric :=
    unary_cont_closed vUnary nUnary normRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed qUnary sUnary cauchyRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed cauchyUnary rUnary completionRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed completionUnary eUnary toleranceRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed toleranceUnary zUnary separatedRoute
  have reduction : BanachSpaceCompleteMetricReduction V N M Q S R E Z := by
    exact
      ⟨vUnary, nUnary, mUnary, qUnary, sUnary, rUnary, eUnary, zUnary,
        normMetric, cauchyRead, completionRead, toleranceRead, separatedRead,
        normRoute, cauchyRoute, completionRoute, toleranceRoute, separatedRoute⟩
  exact ⟨reduction, normUnary, cauchyUnary, completionUnary, toleranceUnary, separatedUnary⟩

end BEDC.Derived.BanachSpaceUp
