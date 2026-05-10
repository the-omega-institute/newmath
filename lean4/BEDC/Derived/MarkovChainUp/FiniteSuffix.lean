import BEDC.Derived.MarkovChainUp

namespace BEDC.Derived.MarkovChainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem MarkovChainTransitionPacket_finite_suffix_carrier
    {source time boundary next law transition provenance ledger suffixLedger : BHist} :
    MarkovChainTransitionPacket source time boundary next law transition provenance ledger ->
      UnaryHistory suffixLedger ->
        Cont boundary suffixLedger next ->
          Cont provenance law ledger ->
            MarkovChainTransitionPacket source suffixLedger boundary next law transition provenance
              ledger := by
  intro packet suffixUnary boundarySuffix ledgerCont
  have _nextUnaryFromSuffix : UnaryHistory next :=
    unary_cont_closed packet.left.left suffixUnary boundarySuffix
  exact
    And.intro packet.left
      (And.intro suffixUnary
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro packet.right.right.right.right.left ledgerCont))))

end BEDC.Derived.MarkovChainUp
