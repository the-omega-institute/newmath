import BEDC.Derived.CompilerCompositionTraceUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.CompilerCompositionTraceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem CompilerCompositionTrace_associativity
    {K01 K12 K23 leftPair leftComposite rightPair rightComposite : BHist} :
    Cont K01 K12 leftPair →
      Cont leftPair K23 leftComposite →
        Cont K12 K23 rightPair →
          Cont K01 rightPair rightComposite → hsame leftComposite rightComposite := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro routeLeftPair routeLeftComposite routeRightPair routeRightComposite
  cases routeLeftPair
  cases routeLeftComposite
  cases routeRightPair
  cases routeRightComposite
  exact append_assoc K01 K12 K23

end BEDC.Derived.CompilerCompositionTraceUp
