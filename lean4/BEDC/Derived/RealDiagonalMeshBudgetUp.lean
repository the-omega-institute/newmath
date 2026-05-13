import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealDiagonalMeshBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def RealDiagonalMeshBudgetCarrier
    (q b omega rho delta theta e h c p n : BHist) : Prop :=
  UnaryHistory q ∧ UnaryHistory b ∧ UnaryHistory omega ∧ UnaryHistory rho ∧
    UnaryHistory delta ∧ UnaryHistory theta ∧ UnaryHistory e ∧
      Cont q b h ∧ Cont b omega theta ∧ Cont omega rho c ∧ Cont rho delta e ∧
        hsame p p ∧ hsame n n

theorem RealDiagonalMeshBudgetCarrier_namecert_obligations
    {q b omega rho delta theta e h c p n : BHist} :
    RealDiagonalMeshBudgetCarrier q b omega rho delta theta e h c p n ->
      UnaryHistory q /\ UnaryHistory b /\ UnaryHistory omega /\ UnaryHistory rho /\
        UnaryHistory delta /\ UnaryHistory theta /\ UnaryHistory e /\ Cont q b h /\
          Cont omega rho c /\ hsame p p /\ hsame n n := by
  intro carrier
  obtain ⟨qUnary, bUnary, omegaUnary, rhoUnary, deltaUnary, thetaUnary, eUnary,
    qbRoute, _budgetWindowRoute, omegaReadbackRoute, _readbackLedgerRoute,
    provenanceSame, nameSame⟩ := carrier
  exact
    ⟨qUnary, bUnary, omegaUnary, rhoUnary, deltaUnary, thetaUnary, eUnary,
      qbRoute, omegaReadbackRoute, provenanceSame, nameSame⟩

theorem RealDiagonalMeshBudgetCarrier_window_coverage
    {q b omega rho delta theta e h c p n : BHist} :
    RealDiagonalMeshBudgetCarrier q b omega rho delta theta e h c p n ->
      Cont b omega theta ->
        UnaryHistory b /\ UnaryHistory omega /\ UnaryHistory rho /\ UnaryHistory delta /\
          UnaryHistory theta /\ hsame theta theta := by
  intro carrier selectedWindowRoute
  obtain ⟨_qUnary, bUnary, omegaUnary, rhoUnary, deltaUnary, _thetaUnary, _eUnary,
    _qbRoute, _budgetWindowRoute, _omegaReadbackRoute, _readbackLedgerRoute,
    _provenanceSame, _nameSame⟩ := carrier
  have thetaUnary : UnaryHistory theta :=
    unary_cont_closed bUnary omegaUnary selectedWindowRoute
  exact
    ⟨bUnary, omegaUnary, rhoUnary, deltaUnary, thetaUnary, hsame_refl theta⟩

end BEDC.Derived.RealDiagonalMeshBudgetUp
