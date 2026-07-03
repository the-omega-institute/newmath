import BEDC.Derived.RegSeqRatUp

namespace BEDC.Derived.RegSeqRatUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RegseqratFiniteRequestTerminalBudgetFactorization
    {schedule endpoint radius distance classifier regularity sealRow terminalRow : BHist} :
    Cont schedule endpoint radius →
      Cont radius distance classifier →
        Cont classifier regularity sealRow →
          Cont schedule sealRow terminalRow →
            hsame terminalRow
              (append schedule (append (append (append schedule endpoint) distance) regularity)) := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro scheduleEndpoint endpointDistance classifierRegularity scheduleSeal
  cases scheduleEndpoint
  cases endpointDistance
  cases classifierRegularity
  cases scheduleSeal
  rfl

end BEDC.Derived.RegSeqRatUp
