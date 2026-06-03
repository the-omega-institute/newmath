import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICCriticalPathFrontierBudgetFactorization [AskSetup] [PackageSetup]
    (strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead l10Budget closedRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
      transport route provenance localName bundle pkg ∧
    Cont strongNorm normalForm candidateRead ∧
      Cont candidateRead dischargeSocket l10Budget ∧
        Cont l10Budget route closedRead ∧
          PkgSig bundle l10Budget pkg ∧ PkgSig bundle closedRead pkg ∧
            UnaryHistory candidateRead ∧ UnaryHistory l10Budget ∧
              UnaryHistory closedRead

end BEDC.Derived.MetaCICCriticalPathUp
