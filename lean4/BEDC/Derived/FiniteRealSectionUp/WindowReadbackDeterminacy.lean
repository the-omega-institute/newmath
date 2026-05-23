import BEDC.Derived.FiniteRealSectionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteRealSectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem FiniteRealSection_window_readback_determinacy [AskSetup] [PackageSetup]
    {q W R D E H C P N qW qW' qWR : BHist} :
    FieldFaithful.fields (FiniteRealSectionUp.mk q W R D E H C P N) =
        [q, W, R, D, E, H, C, P, N] →
      UnaryHistory q →
        UnaryHistory W →
          UnaryHistory R →
            Cont q W qW →
              Cont q W qW' →
                Cont qW R qWR →
                  hsame qW' qW ∧ UnaryHistory qWR ∧ Cont qW R qWR := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory FieldFaithful
  intro _fields qUnary WUnary RUnary qWindow qWindow' qWindowReadback
  have sameWindowRead : hsame qW' qW :=
    cont_deterministic qWindow' qWindow
  have qWUnary : UnaryHistory qW :=
    unary_cont_closed qUnary WUnary qWindow
  have qWRUnary : UnaryHistory qWR :=
    unary_cont_closed qWUnary RUnary qWindowReadback
  exact ⟨sameWindowRead, qWRUnary, qWindowReadback⟩

end BEDC.Derived.FiniteRealSectionUp
