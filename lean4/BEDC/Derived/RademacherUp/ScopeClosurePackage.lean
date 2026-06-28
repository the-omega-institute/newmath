import BEDC.Derived.RademacherUp.DifferenceWindowObligation
import BEDC.Derived.RademacherUp.KernelScope

namespace BEDC.Derived.RademacherUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem RademacherCarrier_scope_closure_package
    {L E D M A H C P N metricRead lipschitzRead dyadicMetricRead derivativeRead
      sealedRead replayRead : BHist} :
    RademacherCarrier L E D M A H C P N ->
      Cont L M metricRead ->
        Cont metricRead A lipschitzRead ->
          Cont D M dyadicMetricRead ->
            Cont D lipschitzRead derivativeRead ->
              Cont derivativeRead E sealedRead ->
                Cont sealedRead H replayRead ->
                  SemanticNameCert
                      (fun row : BHist =>
                        (hsame row derivativeRead ∨ hsame row sealedRead ∨
                            hsame row replayRead) ∧
                          UnaryHistory row)
                      (fun row : BHist =>
                        hsame row L ∨ hsame row D ∨ hsame row M ∨ hsame row A ∨
                          hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row derivativeRead ∨
                              hsame row sealedRead ∨ hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont L M metricRead ∧
                          Cont metricRead A lipschitzRead ∧
                            Cont D lipschitzRead derivativeRead ∧
                              Cont derivativeRead E sealedRead ∧
                                Cont sealedRead H replayRead)
                      hsame ∧
                    UnaryHistory metricRead ∧ UnaryHistory lipschitzRead ∧
                      UnaryHistory derivativeRead ∧ UnaryHistory sealedRead ∧
                        UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier metricRoute lipschitzRoute _dyadicMetricRoute derivativeRoute sealedRoute
    replayRoute
  obtain ⟨lUnary, eUnary, dUnary, mUnary, aUnary, hUnary, _cUnary, _pUnary,
    _nUnary, _packetWitness⟩ := carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed lUnary mUnary metricRoute
  have lipschitzUnary : UnaryHistory lipschitzRead :=
    unary_cont_closed metricUnary aUnary lipschitzRoute
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed dUnary lipschitzUnary derivativeRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed derivativeUnary eUnary sealedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sealedUnary hUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row derivativeRead ∨ hsame row sealedRead ∨ hsame row replayRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row D ∨ hsame row M ∨ hsame row A ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row derivativeRead ∨ hsame row sealedRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L M metricRead ∧ Cont metricRead A lipschitzRead ∧
              Cont D lipschitzRead derivativeRead ∧ Cont derivativeRead E sealedRead ∧
                Cont sealedRead H replayRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro derivativeRead ⟨Or.inl (hsame_refl derivativeRead), derivativeUnary⟩
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
        intro row other sameRows source
        have lift : ∀ {target : BHist}, hsame row target -> hsame other target := by
          intro target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases source.left with
          | inl sameDerivative =>
              exact Or.inl (lift sameDerivative)
          | inr rest =>
              cases rest with
              | inl sameSealed =>
                  exact Or.inr (Or.inl (lift sameSealed))
              | inr sameReplay =>
                  exact Or.inr (Or.inr (lift sameReplay))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameDerivative =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inl sameDerivative)))))))))
      | inr rest =>
          cases rest with
          | inl sameSealed =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr (Or.inl sameSealed))))))))))
          | inr sameReplay =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr (Or.inr sameReplay))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, metricRoute, lipschitzRoute, derivativeRoute, sealedRoute,
          replayRoute⟩
  }
  exact ⟨cert, metricUnary, lipschitzUnary, derivativeUnary, sealedUnary, replayUnary⟩

end BEDC.Derived.RademacherUp
