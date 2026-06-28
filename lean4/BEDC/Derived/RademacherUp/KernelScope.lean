import BEDC.Derived.RademacherUp

namespace BEDC.Derived.RademacherUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RademacherCarrier_kernel_scope
    {L E D M A H C P N dyadicMetricRead lipschitzControlRead realRead replayRead
      nameRead : BHist} :
    RademacherCarrier L E D M A H C P N →
      Cont D M dyadicMetricRead →
        Cont L A lipschitzControlRead →
          Cont dyadicMetricRead lipschitzControlRead realRead →
            Cont realRead C replayRead →
              Cont P N nameRead →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row realRead ∨ hsame row replayRead ∨ hsame row nameRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row D ∨ hsame row M ∨ hsame row L ∨ hsame row A ∨
                        hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row realRead ∨
                          hsame row replayRead ∨ hsame row nameRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ RademacherCarrier L E D M A H C P N ∧
                        Cont D M dyadicMetricRead ∧ Cont L A lipschitzControlRead ∧
                          Cont dyadicMetricRead lipschitzControlRead realRead ∧
                            Cont realRead C replayRead ∧ Cont P N nameRead)
                    hsame ∧
                  UnaryHistory realRead ∧ UnaryHistory replayRead ∧
                    UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrierData dyadicMetricRoute lipschitzControlRoute realRoute replayRoute nameRoute
  have carrierOriginal : RademacherCarrier L E D M A H C P N := carrierData
  obtain ⟨lUnary, _eUnary, dUnary, mUnary, aUnary, _hUnary, cUnary, pUnary,
    nUnary, _packetWitness⟩ := carrierData
  have dyadicMetricUnary : UnaryHistory dyadicMetricRead :=
    unary_cont_closed dUnary mUnary dyadicMetricRoute
  have lipschitzControlUnary : UnaryHistory lipschitzControlRead :=
    unary_cont_closed lUnary aUnary lipschitzControlRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicMetricUnary lipschitzControlUnary realRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed realUnary cUnary replayRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed pUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row realRead ∨ hsame row replayRead ∨ hsame row nameRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row M ∨ hsame row L ∨ hsame row A ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row realRead ∨
                hsame row replayRead ∨ hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ RademacherCarrier L E D M A H C P N ∧
              Cont D M dyadicMetricRead ∧ Cont L A lipschitzControlRead ∧
                Cont dyadicMetricRead lipschitzControlRead realRead ∧
                  Cont realRead C replayRead ∧ Cont P N nameRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨Or.inr (Or.inl (hsame_refl replayRead)), replayUnary⟩
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
        intro row other sameRows sourceRow
        have lift : ∀ {target : BHist}, hsame row target → hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases sourceRow.left with
          | inl sameReal =>
              exact Or.inl (lift sameReal)
          | inr rest =>
              cases rest with
              | inl sameReplay =>
                  exact Or.inr (Or.inl (lift sameReplay))
              | inr sameName =>
                  exact Or.inr (Or.inr (lift sameName))
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameReal =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inl sameReal)))))))
      | inr rest =>
          cases rest with
          | inl sameReplay =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inl sameReplay))))))))
          | inr sameName =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr sameName))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, carrierOriginal, dyadicMetricRoute, lipschitzControlRoute,
          realRoute, replayRoute, nameRoute⟩
  }
  exact ⟨cert, realUnary, replayUnary, nameUnary⟩

end BEDC.Derived.RademacherUp
