import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
import BEDC.Derived.RealObservationBudgetUp.TasteGate

namespace BEDC.Derived.RealDiagonalMeshBudgetUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def RealDiagonalMeshBudgetCarrier
    (q b omega rho delta theta e h c p n : BHist) : Prop :=
  UnaryHistory q ∧ UnaryHistory b ∧ UnaryHistory omega ∧ UnaryHistory rho ∧
    UnaryHistory delta ∧ UnaryHistory theta ∧ UnaryHistory e ∧
      Cont q b h ∧ Cont b omega theta ∧ Cont omega rho c ∧ Cont rho delta e ∧
        UnaryHistory p ∧ hsame p p ∧ hsame n n

theorem RealDiagonalMeshBudgetCarrier_namecert_obligations
    {q b omega rho delta theta e h c p n : BHist} :
    RealDiagonalMeshBudgetCarrier q b omega rho delta theta e h c p n ->
      UnaryHistory q /\ UnaryHistory b /\ UnaryHistory omega /\ UnaryHistory rho /\
        UnaryHistory delta /\ UnaryHistory theta /\ UnaryHistory e /\ Cont q b h /\
          Cont omega rho c /\ hsame p p /\ hsame n n := by
  intro carrier
  obtain ⟨qUnary, bUnary, omegaUnary, rhoUnary, deltaUnary, thetaUnary, eUnary,
    qbRoute, _budgetWindowRoute, omegaReadbackRoute, _readbackLedgerRoute,
    _provenanceUnary, provenanceSame, nameSame⟩ := carrier
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
    _provenanceUnary, _provenanceSame, _nameSame⟩ := carrier
  have thetaUnary : UnaryHistory theta :=
    unary_cont_closed bUnary omegaUnary selectedWindowRoute
  exact
    ⟨bUnary, omegaUnary, rhoUnary, deltaUnary, thetaUnary, hsame_refl theta⟩

theorem RealDiagonalMeshBudgetCarrier_selected_window_refinement
    {q b omega rho delta theta e h c p n : BHist} :
    RealDiagonalMeshBudgetCarrier q b omega rho delta theta e h c p n ->
      UnaryHistory h ∧ UnaryHistory theta ∧ UnaryHistory c ∧ UnaryHistory e ∧
        Cont q b h ∧ Cont b omega theta ∧ Cont omega rho c ∧ Cont rho delta e ∧
          hsame p p ∧ hsame n n := by
  intro carrier
  obtain ⟨qUnary, bUnary, omegaUnary, rhoUnary, _deltaUnary, thetaUnary, eUnary,
    precisionBudgetRoute, budgetWindowRoute, windowReadbackRoute, readbackLedgerRoute,
    _provenanceUnary, provenanceSame, nameSame⟩ := carrier
  have hUnary : UnaryHistory h :=
    unary_cont_closed qUnary bUnary precisionBudgetRoute
  have cUnary : UnaryHistory c :=
    unary_cont_closed omegaUnary rhoUnary windowReadbackRoute
  exact
    ⟨hUnary, thetaUnary, cUnary, eUnary, precisionBudgetRoute, budgetWindowRoute,
      windowReadbackRoute, readbackLedgerRoute, provenanceSame, nameSame⟩

theorem RealDiagonalMeshBudgetCarrier_realup_handoff
    {q b omega rho delta theta e h c p n sealConsumer : BHist} :
    RealDiagonalMeshBudgetCarrier q b omega rho delta theta e h c p n ->
      Cont theta e sealConsumer ->
        UnaryHistory q /\ UnaryHistory b /\ UnaryHistory omega /\ UnaryHistory rho /\
          UnaryHistory delta /\ UnaryHistory theta /\ UnaryHistory e /\
            UnaryHistory sealConsumer /\ Cont theta e sealConsumer /\ hsame p p /\
              hsame n n := by
  intro carrier sealRoute
  obtain ⟨qUnary, bUnary, omegaUnary, rhoUnary, deltaUnary, thetaUnary, eUnary,
    _qbRoute, _budgetWindowRoute, _omegaReadbackRoute, _readbackLedgerRoute,
    _provenanceUnary, provenanceSame, nameSame⟩ := carrier
  have sealUnary : UnaryHistory sealConsumer :=
    unary_cont_closed thetaUnary eUnary sealRoute
  exact
    ⟨qUnary, bUnary, omegaUnary, rhoUnary, deltaUnary, thetaUnary, eUnary, sealUnary,
      sealRoute, provenanceSame, nameSame⟩

theorem RealDiagonalMeshBudgetCarrier_seal_route_exactness
    {q b omega rho delta theta e h c p n sealConsumer : BHist} :
    RealDiagonalMeshBudgetCarrier q b omega rho delta theta e h c p n ->
      Cont theta e sealConsumer ->
        UnaryHistory q /\ UnaryHistory b /\ UnaryHistory omega /\ UnaryHistory rho /\
          UnaryHistory delta /\ UnaryHistory theta /\ UnaryHistory e /\
            UnaryHistory sealConsumer /\ Cont q b h /\ Cont b omega theta /\
              Cont omega rho c /\ Cont rho delta e /\ Cont theta e sealConsumer /\
                hsame p p /\ hsame n n := by
  intro carrier sealRoute
  obtain ⟨qUnary, bUnary, omegaUnary, rhoUnary, deltaUnary, thetaUnary, eUnary,
    qbRoute, budgetWindowRoute, omegaReadbackRoute, readbackLedgerRoute,
    _provenanceUnary, provenanceSame, nameSame⟩ := carrier
  have sealUnary : UnaryHistory sealConsumer :=
    unary_cont_closed thetaUnary eUnary sealRoute
  exact
    ⟨qUnary, bUnary, omegaUnary, rhoUnary, deltaUnary, thetaUnary, eUnary, sealUnary,
      qbRoute, budgetWindowRoute, omegaReadbackRoute, readbackLedgerRoute, sealRoute,
      provenanceSame, nameSame⟩

theorem RealDiagonalMeshBudgetCarrier_consumer_scope_exhaustion
    {q b omega rho delta theta e h c p n sealConsumer downstreamConsumer : BHist} :
    RealDiagonalMeshBudgetCarrier q b omega rho delta theta e h c p n →
      Cont theta e sealConsumer →
        Cont sealConsumer p downstreamConsumer →
          UnaryHistory sealConsumer ∧ UnaryHistory downstreamConsumer ∧ Cont q b h ∧
            Cont b omega theta ∧ Cont omega rho c ∧ Cont rho delta e ∧
              Cont theta e sealConsumer ∧ Cont sealConsumer p downstreamConsumer ∧
                hsame p p ∧ hsame n n := by
  intro carrier sealRoute downstreamRoute
  obtain ⟨_qUnary, _bUnary, omegaUnary, rhoUnary, _deltaUnary, thetaUnary, eUnary,
    qbRoute, budgetWindowRoute, omegaReadbackRoute, readbackLedgerRoute,
    provenanceUnary, provenanceSame, nameSame⟩ := carrier
  have sealUnary : UnaryHistory sealConsumer :=
    unary_cont_closed thetaUnary eUnary sealRoute
  have downstreamUnary : UnaryHistory downstreamConsumer :=
    unary_cont_closed sealUnary provenanceUnary downstreamRoute
  exact
    ⟨sealUnary, downstreamUnary, qbRoute, budgetWindowRoute, omegaReadbackRoute,
      readbackLedgerRoute, sealRoute, downstreamRoute, provenanceSame, nameSame⟩

theorem RealDiagonalMeshBudgetCarrier_observation_budget_handoff
    {q b omega rho delta theta e h c p n sealConsumer observationConsumer : BHist} :
    RealDiagonalMeshBudgetCarrier q b omega rho delta theta e h c p n ->
      Cont theta e sealConsumer ->
        Cont e p observationConsumer ->
          (∃ obs : BEDC.Derived.RealObservationBudgetUp.RealObservationBudgetUp,
              obs =
                BEDC.Derived.RealObservationBudgetUp.RealObservationBudgetUp.mk q omega delta rho
                  e h c p n) ∧
            UnaryHistory sealConsumer ∧ UnaryHistory observationConsumer ∧
              Cont theta e sealConsumer ∧ Cont e p observationConsumer ∧ hsame p p ∧
                hsame n n := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro carrier sealRoute observationRoute
  obtain ⟨_qUnary, _bUnary, _omegaUnary, _rhoUnary, _deltaUnary, thetaUnary, eUnary,
    _qbRoute, _budgetWindowRoute, _omegaReadbackRoute, _readbackLedgerRoute,
    provenanceUnary, provenanceSame, nameSame⟩ := carrier
  have sealUnary : UnaryHistory sealConsumer :=
    unary_cont_closed thetaUnary eUnary sealRoute
  have observationUnary : UnaryHistory observationConsumer :=
    unary_cont_closed eUnary provenanceUnary observationRoute
  exact
    ⟨⟨BEDC.Derived.RealObservationBudgetUp.RealObservationBudgetUp.mk q omega delta rho e h c p n,
      rfl⟩, sealUnary, observationUnary, sealRoute, observationRoute, provenanceSame,
      nameSame⟩

theorem RealDiagonalMeshBudgetCarrier_budget_monotonicity
    {q b bPrime omega rho delta theta e h hPrime c p n : BHist} :
    RealDiagonalMeshBudgetCarrier q b omega rho delta theta e h c p n ->
      UnaryHistory bPrime ->
        Cont q bPrime hPrime ->
          Cont bPrime omega theta ->
            hsame h hPrime ->
              UnaryHistory hPrime ∧ UnaryHistory theta ∧ UnaryHistory c ∧
                UnaryHistory e ∧ Cont q bPrime hPrime ∧ Cont bPrime omega theta ∧
                  Cont omega rho c ∧ Cont rho delta e ∧ hsame h hPrime ∧ hsame p p ∧
                    hsame n n := by
  intro carrier bPrimeUnary enlargedBudgetRoute enlargedWindowRoute sameBudgetResult
  obtain ⟨qUnary, _bUnary, omegaUnary, rhoUnary, _deltaUnary, _thetaUnary, eUnary,
    _qbRoute, _budgetWindowRoute, omegaReadbackRoute, readbackLedgerRoute,
    _provenanceUnary, provenanceSame, nameSame⟩ := carrier
  have hPrimeUnary : UnaryHistory hPrime :=
    unary_cont_closed qUnary bPrimeUnary enlargedBudgetRoute
  have thetaUnary : UnaryHistory theta :=
    unary_cont_closed bPrimeUnary omegaUnary enlargedWindowRoute
  have cUnary : UnaryHistory c :=
    unary_cont_closed omegaUnary rhoUnary omegaReadbackRoute
  exact
    ⟨hPrimeUnary, thetaUnary, cUnary, eUnary, enlargedBudgetRoute,
      enlargedWindowRoute, omegaReadbackRoute, readbackLedgerRoute, sameBudgetResult,
      provenanceSame, nameSame⟩

theorem RealDiagonalMeshBudgetCarrier_nonescape
    {q b omega rho delta theta e h c p n sealConsumer downstreamConsumer : BHist} :
    RealDiagonalMeshBudgetCarrier q b omega rho delta theta e h c p n ->
      Cont theta e sealConsumer ->
        Cont sealConsumer p downstreamConsumer ->
          UnaryHistory q ∧ UnaryHistory b ∧ UnaryHistory omega ∧ UnaryHistory rho ∧
            UnaryHistory delta ∧ UnaryHistory theta ∧ UnaryHistory e ∧
              UnaryHistory sealConsumer ∧ UnaryHistory downstreamConsumer ∧ Cont q b h ∧
                Cont b omega theta ∧ Cont omega rho c ∧ Cont rho delta e ∧
                  Cont theta e sealConsumer ∧ Cont sealConsumer p downstreamConsumer ∧
                    hsame p p ∧ hsame n n := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro carrier sealRoute downstreamRoute
  obtain ⟨qUnary, bUnary, omegaUnary, rhoUnary, deltaUnary, thetaUnary, eUnary,
    qbRoute, budgetWindowRoute, omegaReadbackRoute, readbackLedgerRoute,
    provenanceUnary, provenanceSame, nameSame⟩ := carrier
  have sealUnary : UnaryHistory sealConsumer :=
    unary_cont_closed thetaUnary eUnary sealRoute
  have downstreamUnary : UnaryHistory downstreamConsumer :=
    unary_cont_closed sealUnary provenanceUnary downstreamRoute
  exact
    ⟨qUnary, bUnary, omegaUnary, rhoUnary, deltaUnary, thetaUnary, eUnary,
      sealUnary, downstreamUnary, qbRoute, budgetWindowRoute, omegaReadbackRoute,
      readbackLedgerRoute, sealRoute, downstreamRoute, provenanceSame, nameSame⟩

theorem RealDiagonalMeshBudgetCarrier_common_refinement_seal
    {q b omega rho delta theta e h c p n sealConsumer sharedThreshold sharedRoute
      diagonalRoute : BHist} :
    RealDiagonalMeshBudgetCarrier q b omega rho delta theta e h c p n ->
      Cont theta e sealConsumer ->
        Cont omega delta sharedThreshold ->
          Cont sharedThreshold e sharedRoute ->
            Cont theta sharedThreshold diagonalRoute ->
              UnaryHistory sealConsumer ∧ UnaryHistory sharedThreshold ∧
                UnaryHistory sharedRoute ∧ UnaryHistory diagonalRoute ∧
                  Cont theta e sealConsumer ∧ Cont omega delta sharedThreshold ∧
                    Cont sharedThreshold e sharedRoute ∧
                      Cont theta sharedThreshold diagonalRoute ∧ hsame p p ∧ hsame n n := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro carrier sealRoute thresholdRoute sharedSealRoute diagonalThresholdRoute
  obtain ⟨_qUnary, _bUnary, omegaUnary, _rhoUnary, deltaUnary, thetaUnary, eUnary,
    _qbRoute, _budgetWindowRoute, _omegaReadbackRoute, _readbackLedgerRoute,
    _provenanceUnary, provenanceSame, nameSame⟩ := carrier
  have sealUnary : UnaryHistory sealConsumer :=
    unary_cont_closed thetaUnary eUnary sealRoute
  have thresholdUnary : UnaryHistory sharedThreshold :=
    unary_cont_closed omegaUnary deltaUnary thresholdRoute
  have sharedRouteUnary : UnaryHistory sharedRoute :=
    unary_cont_closed thresholdUnary eUnary sharedSealRoute
  have diagonalRouteUnary : UnaryHistory diagonalRoute :=
    unary_cont_closed thetaUnary thresholdUnary diagonalThresholdRoute
  exact
    ⟨sealUnary, thresholdUnary, sharedRouteUnary, diagonalRouteUnary, sealRoute,
      thresholdRoute, sharedSealRoute, diagonalThresholdRoute, provenanceSame, nameSame⟩

end BEDC.Derived.RealDiagonalMeshBudgetUp
