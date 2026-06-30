import BEDC.Derived.CofinalStreamTailSelectorUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CofinalStreamTailSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CofinalStreamTailSelectorWindowReadbackScope
    {request window regular dyadic real selector transport replay provenance name readback
      sealRead : BHist} :
    Cont window regular readback →
      Cont readback dyadic sealRead →
        hsame window window ∧ hsame regular regular ∧ hsame dyadic dyadic ∧
            hsame real real ∧ UnaryHistory readback →
          ∃ x : CofinalStreamTailSelectorUp,
            x =
              CofinalStreamTailSelectorUp.mk request window regular dyadic real selector transport
                replay provenance name := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro _windowRegularReadback _readbackDyadicSeal displayedReadback
  obtain ⟨_windowStable, _regularStable, _dyadicStable, _realStable, _readbackUnary⟩ :=
    displayedReadback
  exact
    Exists.intro
      (CofinalStreamTailSelectorUp.mk request window regular dyadic real selector transport replay
        provenance name)
      rfl

end BEDC.Derived.CofinalStreamTailSelectorUp
