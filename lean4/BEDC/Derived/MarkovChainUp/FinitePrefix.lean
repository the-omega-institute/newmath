import BEDC.Derived.MarkovChainUp

namespace BEDC.Derived.MarkovChainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def MarkovChainFinitePrefixRestriction
    (source time current next law transition provenance ledger prefixTime prefixCurrent prefixNext
      prefixLaw prefixTransition prefixProvenance prefixLedger : BHist) : Prop :=
  MarkovChainTransitionPacket source time current next law transition provenance ledger ∧
    UnaryHistory prefixTime ∧ hsame current prefixCurrent ∧ hsame next prefixNext ∧
      hsame law prefixLaw ∧ hsame transition prefixTransition ∧
        Cont prefixCurrent prefixTransition prefixProvenance ∧
          Cont prefixProvenance prefixLaw prefixLedger

end BEDC.Derived.MarkovChainUp
