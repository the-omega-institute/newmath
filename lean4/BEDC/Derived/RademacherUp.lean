import BEDC.Derived.RademacherUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.RademacherUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def RademacherCarrier (L E D M A H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory
  UnaryHistory L ∧ UnaryHistory E ∧ UnaryHistory D ∧ UnaryHistory M ∧
    UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧
        ∃ packet : RademacherUp,
          packet = RademacherUp.mk L E D M A H C P N

theorem RademacherCarrier_finite_derivative_candidate_packet
    {L E D M A H C P N dyadicMetricRead lipschitzControlRead realRead : BHist} :
    RademacherCarrier L E D M A H C P N →
      Cont D M dyadicMetricRead →
        Cont L A lipschitzControlRead →
          Cont dyadicMetricRead lipschitzControlRead realRead →
            SemanticNameCert
                (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row D ∨ hsame row M ∨ hsame row L ∨ hsame row A ∨
                    hsame row E ∨ hsame row realRead)
                (fun row : BHist =>
                  hsame row realRead ∧ Cont D M dyadicMetricRead ∧
                    Cont L A lipschitzControlRead ∧
                      Cont dyadicMetricRead lipschitzControlRead realRead)
                hsame ∧
              UnaryHistory dyadicMetricRead ∧ UnaryHistory lipschitzControlRead ∧
                UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier dyadicMetricRoute lipschitzControlRoute realRoute
  obtain ⟨lUnary, _eUnary, dUnary, mUnary, aUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _packetWitness⟩ := carrier
  have dyadicMetricUnary : UnaryHistory dyadicMetricRead :=
    unary_cont_closed dUnary mUnary dyadicMetricRoute
  have lipschitzControlUnary : UnaryHistory lipschitzControlRead :=
    unary_cont_closed lUnary aUnary lipschitzControlRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicMetricUnary lipschitzControlUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row M ∨ hsame row L ∨ hsame row A ∨
              hsame row E ∨ hsame row realRead)
          (fun row : BHist =>
            hsame row realRead ∧ Cont D M dyadicMetricRead ∧
              Cont L A lipschitzControlRead ∧
                Cont dyadicMetricRead lipschitzControlRead realRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, dyadicMetricRoute, lipschitzControlRoute, realRoute⟩
  }
  exact ⟨cert, dyadicMetricUnary, lipschitzControlUnary, realUnary⟩

theorem RademacherCarrier_absolute_continuity_boundary
    {L E D M A H C P N variationWindow sealedWindow : BHist} :
    RademacherCarrier L E D M A H C P N →
      Cont L A variationWindow →
        Cont variationWindow E sealedWindow →
          SemanticNameCert
              (fun row : BHist => hsame row sealedWindow ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row L ∨ hsame row A ∨ hsame row variationWindow ∨ hsame row E ∨
                  hsame row sealedWindow)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont L A variationWindow ∧
                  Cont variationWindow E sealedWindow)
              hsame ∧
            UnaryHistory variationWindow ∧ UnaryHistory sealedWindow := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier variationRoute sealRoute
  obtain ⟨lUnary, eUnary, _dUnary, _mUnary, aUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _packetWitness⟩ := carrier
  have variationUnary : UnaryHistory variationWindow :=
    unary_cont_closed lUnary aUnary variationRoute
  have sealedUnary : UnaryHistory sealedWindow :=
    unary_cont_closed variationUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row A ∨ hsame row variationWindow ∨ hsame row E ∨
              hsame row sealedWindow)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L A variationWindow ∧
              Cont variationWindow E sealedWindow)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealedWindow ⟨hsame_refl sealedWindow, sealedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, variationRoute, sealRoute⟩
  }
  exact ⟨cert, variationUnary, sealedUnary⟩

theorem RademacherCarrier_difference_quotient_window_stability
    {L E D M A H C P N L' E' D' M' A' H' C' P' N'
      dyadicMetricRead lipschitzControlRead realRead
      dyadicMetricRead' lipschitzControlRead' realRead' : BHist} :
    RademacherCarrier L E D M A H C P N →
      RademacherCarrier L' E' D' M' A' H' C' P' N' →
        Cont D M dyadicMetricRead →
          Cont L A lipschitzControlRead →
            Cont dyadicMetricRead lipschitzControlRead realRead →
              Cont D' M' dyadicMetricRead' →
                Cont L' A' lipschitzControlRead' →
                  Cont dyadicMetricRead' lipschitzControlRead' realRead' →
                    hsame D D' →
                      hsame M M' →
                        hsame L L' →
                          hsame A A' →
                            hsame E E' →
                              UnaryHistory realRead ∧ UnaryHistory realRead' ∧
                                SemanticNameCert
                                  (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row D ∨ hsame row M ∨ hsame row L ∨
                                      hsame row A ∨ hsame row E ∨ hsame row realRead)
                                  (fun row : BHist =>
                                    hsame row realRead ∧ Cont D M dyadicMetricRead ∧
                                      Cont L A lipschitzControlRead ∧
                                        Cont dyadicMetricRead lipschitzControlRead realRead)
                                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier carrier' dyadicMetricRoute lipschitzControlRoute realRoute
  intro dyadicMetricRoute' lipschitzControlRoute' realRoute'
  intro _sameD _sameM _sameL _sameA _sameE
  have packet :=
    RademacherCarrier_finite_derivative_candidate_packet
      carrier dyadicMetricRoute lipschitzControlRoute realRoute
  have packet' :=
    RademacherCarrier_finite_derivative_candidate_packet
      carrier' dyadicMetricRoute' lipschitzControlRoute' realRoute'
  exact ⟨packet.right.right.right, packet'.right.right.right, packet.left⟩

theorem RademacherCarrier_lipschitz_metric_scope
    {L E D M A H C P N metricRead lipschitzRead derivativeRead : BHist} :
    RademacherCarrier L E D M A H C P N →
      Cont L M metricRead →
        Cont metricRead A lipschitzRead →
          Cont D lipschitzRead derivativeRead →
            SemanticNameCert
                (fun row : BHist => hsame row derivativeRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row L ∨ hsame row M ∨ hsame row A ∨ hsame row D ∨
                    hsame row derivativeRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont L M metricRead ∧
                    Cont metricRead A lipschitzRead ∧
                      Cont D lipschitzRead derivativeRead)
                hsame ∧
              UnaryHistory metricRead ∧ UnaryHistory lipschitzRead ∧
                UnaryHistory derivativeRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier metricRoute lipschitzRoute derivativeRoute
  obtain ⟨lUnary, _eUnary, dUnary, mUnary, aUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _packetWitness⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed lUnary mUnary metricRoute
  have lipschitzUnary : UnaryHistory lipschitzRead :=
    unary_cont_closed metricUnary aUnary lipschitzRoute
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed dUnary lipschitzUnary derivativeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row derivativeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row M ∨ hsame row A ∨ hsame row D ∨
              hsame row derivativeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L M metricRead ∧ Cont metricRead A lipschitzRead ∧
              Cont D lipschitzRead derivativeRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro derivativeRead ⟨hsame_refl derivativeRead, derivativeUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, metricRoute, lipschitzRoute, derivativeRoute⟩
  }
  exact ⟨cert, metricUnary, lipschitzUnary, derivativeUnary⟩

end BEDC.Derived.RademacherUp
