import BEDC.Derived.LieAlgebraUp
import BEDC.Derived.LieGroupUp
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.AdjointRepUp

open BEDC.Derived.LieAlgebraUp
open BEDC.Derived.LieGroupUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem AdjointRepSingleton_action_differential_endpoint
    {g x action differential bracket : BHist} :
    LieGroupSingletonCarrier g ->
      LieAlgebraSingletonCarrier x ->
        Cont g x action ->
          Cont BHist.Empty x differential ->
            Cont x x bracket ->
              hsame action BHist.Empty ∧ hsame differential x ∧
                hsame bracket BHist.Empty ∧ UnaryHistory action ∧
                  UnaryHistory differential := by
  intro groupCarrier algebraCarrier actionRow differentialRow bracketRow
  have actionEmpty : hsame action BHist.Empty :=
    cont_respects_hsame groupCarrier algebraCarrier actionRow (cont_left_unit BHist.Empty)
  have differentialSame : hsame differential x :=
    cont_left_unit_result differentialRow
  have bracketEmpty : hsame bracket BHist.Empty :=
    cont_respects_hsame algebraCarrier algebraCarrier bracketRow (cont_left_unit BHist.Empty)
  have actionUnary : UnaryHistory action :=
    unary_transport unary_empty (hsame_symm actionEmpty)
  have differentialUnary : UnaryHistory differential :=
    unary_transport unary_empty (hsame_symm (hsame_trans differentialSame algebraCarrier))
  exact And.intro actionEmpty
    (And.intro differentialSame
      (And.intro bracketEmpty (And.intro actionUnary differentialUnary)))

end BEDC.Derived.AdjointRepUp
