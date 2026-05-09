import BEDC.Derived.GroupUp
import BEDC.Derived.ModuleUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CharacterTheoryUp

open BEDC.Derived.GroupUp
open BEDC.Derived.ModuleUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CharacterTheoryRootBHistSurface_root_carrier_obligation
    {group vector action trace provenance : BHist} :
    GroupSingletonCarrier group ->
      ModuleSingletonCarrier vector ->
        Cont group vector action ->
          Cont action BHist.Empty trace ->
            hsame provenance trace ->
              GroupSingletonCarrier group ∧ ModuleSingletonCarrier vector ∧
                UnaryHistory action ∧ UnaryHistory trace ∧ hsame provenance trace ∧
                  Cont group vector action ∧ Cont action BHist.Empty trace := by
  intro groupCarrier vectorCarrier actionRow traceRow provenanceTrace
  have groupUnary : UnaryHistory group :=
    unary_transport unary_empty (hsame_symm groupCarrier)
  have vectorUnary : UnaryHistory vector :=
    unary_transport unary_empty (hsame_symm vectorCarrier)
  have actionUnary : UnaryHistory action :=
    unary_cont_closed groupUnary vectorUnary actionRow
  have traceUnary : UnaryHistory trace :=
    unary_cont_closed actionUnary unary_empty traceRow
  exact
    ⟨groupCarrier, vectorCarrier, actionUnary, traceUnary, provenanceTrace, actionRow, traceRow⟩

end BEDC.Derived.CharacterTheoryUp
