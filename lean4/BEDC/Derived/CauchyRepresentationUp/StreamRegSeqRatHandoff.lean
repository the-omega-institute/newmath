import BEDC.Derived.CauchyRepresentationUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CauchyRepresentationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyRepresentationStreamRegSeqRatHandoff
    {S W R D A G H C P E N windowRead readbackRead dyadicRead sealRead representedRead : BHist} :
    UnaryHistory S → UnaryHistory W → UnaryHistory R → UnaryHistory D → UnaryHistory A →
      UnaryHistory G → Cont S W windowRead → Cont windowRead R readbackRead →
        Cont readbackRead D dyadicRead → Cont dyadicRead A sealRead →
          Cont sealRead G representedRead →
            cauchyRepresentationFields (CauchyRepresentationUp.mk S W R D A G H C P E N) =
              [S, W, R, D, A, G, H, C, P, E, N] ∧
              UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                UnaryHistory dyadicRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory representedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro unaryS unaryW unaryR unaryD unaryA unaryG
  intro windowRoute readbackRoute dyadicRoute sealRoute representedRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryS unaryW windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary unaryR readbackRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed readbackUnary unaryD dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary unaryA sealRoute
  have representedUnary : UnaryHistory representedRead :=
    unary_cont_closed sealUnary unaryG representedRoute
  exact ⟨rfl, windowUnary, readbackUnary, dyadicUnary, sealUnary, representedUnary⟩

end BEDC.Derived.CauchyRepresentationUp
