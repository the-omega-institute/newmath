import BEDC.Derived.CompactCoverShrinkageLedgerUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactCoverShrinkageLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CompactCoverShrinkageLedger_uniform_modulus_handoff
    {K U F M Q C H P N coverRead foldRead metricRead uniformRead : BHist}
    {packet : CompactCoverShrinkageLedgerUp} :
    compactCoverShrinkageLedgerFields packet = [K, U, F, M, Q, C, H, P, N] ->
      UnaryHistory K ->
        UnaryHistory C ->
          UnaryHistory F ->
            UnaryHistory M ->
              UnaryHistory U ->
                Cont K C coverRead ->
                  Cont coverRead F foldRead ->
                    Cont foldRead M metricRead ->
                      Cont metricRead U uniformRead ->
                        compactCoverShrinkageLedgerFields packet =
                            [K, U, F, M, Q, C, H, P, N] ∧
                          UnaryHistory coverRead ∧ UnaryHistory foldRead ∧
                            UnaryHistory metricRead ∧ UnaryHistory uniformRead ∧
                              Cont K C coverRead ∧ Cont coverRead F foldRead ∧
                                Cont foldRead M metricRead ∧ Cont metricRead U uniformRead ∧
                                  hsame uniformRead (append metricRead U) := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  intro packetFields unaryK unaryC unaryF unaryM unaryU coverRoute foldRoute metricRoute
    uniformRoute
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed unaryK unaryC coverRoute
  have foldReadUnary : UnaryHistory foldRead :=
    unary_cont_closed coverReadUnary unaryF foldRoute
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed foldReadUnary unaryM metricRoute
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed metricReadUnary unaryU uniformRoute
  exact
    ⟨packetFields, coverReadUnary, foldReadUnary, metricReadUnary, uniformReadUnary,
      coverRoute, foldRoute, metricRoute, uniformRoute, uniformRoute⟩

end BEDC.Derived.CompactCoverShrinkageLedgerUp
