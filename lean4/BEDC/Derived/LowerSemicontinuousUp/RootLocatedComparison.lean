import BEDC.Derived.LowerSemicontinuousUp.RealHandoff

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootLocatedComparison [AskSetup] [PackageSetup]
    {W R E O windowRead epigraphRead locatedRead : BHist} :
    UnaryHistory W →
      UnaryHistory R →
        UnaryHistory E →
          UnaryHistory O →
            Cont W R windowRead →
              Cont windowRead E epigraphRead →
                Cont epigraphRead O locatedRead →
                  UnaryHistory windowRead ∧ UnaryHistory epigraphRead ∧
                    UnaryHistory locatedRead ∧ Cont W R windowRead ∧
                      Cont windowRead E epigraphRead ∧ Cont epigraphRead O locatedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro windowSource readbackSource epigraphSource locatedSource windowRoute epigraphRoute
    locatedRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed windowSource readbackSource windowRoute
  have epigraphUnary : UnaryHistory epigraphRead :=
    unary_cont_closed windowUnary epigraphSource epigraphRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed epigraphUnary locatedSource locatedRoute
  exact ⟨windowUnary, epigraphUnary, locatedUnary, windowRoute, epigraphRoute, locatedRoute⟩

end BEDC.Derived.LowerSemicontinuousUp
