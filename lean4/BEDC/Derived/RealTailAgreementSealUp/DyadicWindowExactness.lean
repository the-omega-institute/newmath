import BEDC.Derived.RealTailAgreementSealUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealTailAgreementSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RealTailAgreementSealCarrier_dyadic_window_exactness
    {R S W D A H C P N leftRead rightRead leftDyadic rightDyadic agreement : BHist} :
    RealTailAgreementSealCarrier R S W D A H C P N →
      Cont R W leftRead →
        Cont S W rightRead →
          Cont leftRead D leftDyadic →
            Cont rightRead D rightDyadic →
              Cont leftDyadic A agreement →
                UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory A ∧
                  hsame leftDyadic (append leftRead D) ∧
                    hsame rightDyadic (append rightRead D) ∧
                      hsame agreement (append leftDyadic A) ∧
                        Cont leftRead D leftDyadic ∧
                          Cont rightRead D rightDyadic := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier _leftWindow _rightWindow leftReadDyadic rightReadDyadic
    leftDyadicAgreement
  obtain ⟨_rUnary, _sUnary, wUnary, dUnary, aUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _sourceWindow, _windowAgreement, _agreementRoute, _provenanceSame⟩ :=
    carrier
  exact
    ⟨wUnary, dUnary, aUnary, leftReadDyadic, rightReadDyadic, leftDyadicAgreement,
      leftReadDyadic, rightReadDyadic⟩

end BEDC.Derived.RealTailAgreementSealUp
