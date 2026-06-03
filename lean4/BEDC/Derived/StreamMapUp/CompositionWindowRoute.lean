import BEDC.Derived.StreamMapUp.TasteGate

namespace BEDC.Derived.StreamMapUp
namespace TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem StreamMapCompositionWindowRoute
    {S1 T1 F1 W1 Q1 D1 R1 H1 C1 P1 N1 S2 T2 F2 W2 Q2 D2 R2 H2 C2 P2 N2
      firstWindow intermediateWindow finalWindow : BHist} :
    streamMapFields (StreamMapUp.mk S1 T1 F1 W1 Q1 D1 R1 H1 C1 P1 N1) =
        [S1, T1, F1, W1, Q1, D1, R1, H1, C1, P1, N1] ->
      streamMapFields (StreamMapUp.mk S2 T2 F2 W2 Q2 D2 R2 H2 C2 P2 N2) =
          [S2, T2, F2, W2, Q2, D2, R2, H2, C2, P2, N2] ->
        hsame T1 S2 ->
          UnaryHistory S1 ->
            UnaryHistory F1 ->
              UnaryHistory T1 ->
                UnaryHistory F2 ->
                  Cont S1 F1 firstWindow ->
                    Cont firstWindow T1 intermediateWindow ->
                      Cont intermediateWindow F2 finalWindow ->
                        UnaryHistory firstWindow ∧
                          UnaryHistory intermediateWindow ∧
                            UnaryHistory finalWindow ∧ hsame T1 S2 := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro firstFields secondFields targetSource sourceUnary firstMapUnary targetUnary secondMapUnary
    firstRoute intermediateRoute finalRoute
  cases firstFields
  cases secondFields
  have firstWindowUnary : UnaryHistory firstWindow :=
    unary_cont_closed sourceUnary firstMapUnary firstRoute
  have intermediateUnary : UnaryHistory intermediateWindow :=
    unary_cont_closed firstWindowUnary targetUnary intermediateRoute
  have finalWindowUnary : UnaryHistory finalWindow :=
    unary_cont_closed intermediateUnary secondMapUnary finalRoute
  exact ⟨firstWindowUnary, intermediateUnary, finalWindowUnary, targetSource⟩

end TasteGate
end BEDC.Derived.StreamMapUp
