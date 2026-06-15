import BEDC.Derived.LogicContradictionMetaLoopUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.LogicContradictionMetaLoopUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem LogicContradictionMetaLoop_sibling_dependency_route
    {P R M A T C G N quotientRead auditRead siblingRead : BHist} :
    UnaryHistory P →
      UnaryHistory R →
        UnaryHistory M →
          UnaryHistory A →
            Cont P M quotientRead →
              Cont R A auditRead →
                Cont quotientRead auditRead siblingRead →
                  logicContradictionMetaLoopFields
                        (LogicContradictionMetaLoopUp.mk P R M A T C G N) =
                      [P, R, M, A, T, C, G, N] ∧
                    UnaryHistory quotientRead ∧
                      UnaryHistory auditRead ∧
                        UnaryHistory siblingRead ∧
                          Cont P M quotientRead ∧
                            Cont R A auditRead ∧
                              Cont quotientRead auditRead siblingRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro unaryP unaryR unaryM unaryA contQuotient contAudit contSibling
  have unaryQuotient : UnaryHistory quotientRead :=
    unary_cont_closed unaryP unaryM contQuotient
  have unaryAudit : UnaryHistory auditRead :=
    unary_cont_closed unaryR unaryA contAudit
  have unarySibling : UnaryHistory siblingRead :=
    unary_cont_closed unaryQuotient unaryAudit contSibling
  exact
    ⟨rfl, unaryQuotient, unaryAudit, unarySibling, contQuotient, contAudit,
      contSibling⟩

end BEDC.Derived.LogicContradictionMetaLoopUp
