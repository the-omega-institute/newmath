import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.EnrichedCatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EnrichedCatPublicPacket [AskSetup] [PackageSetup]
    (categoryBoundary monoidalBoundary homObject identity composition transport provenance ledger
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory categoryBoundary ∧
    UnaryHistory monoidalBoundary ∧
      UnaryHistory homObject ∧
        UnaryHistory identity ∧
          UnaryHistory composition ∧
            UnaryHistory transport ∧
              Cont homObject identity composition ∧
                Cont transport provenance ledger ∧
                  Cont ledger monoidalBoundary endpoint ∧
                    PkgSig bundle endpoint pkg

theorem EnrichedCatPublicPacket_source_obligation [AskSetup] [PackageSetup]
    {categoryBoundary monoidalBoundary homObject identity composition transport provenance ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EnrichedCatPublicPacket categoryBoundary monoidalBoundary homObject identity composition
      transport provenance ledger endpoint bundle pkg ->
      UnaryHistory categoryBoundary ∧
        UnaryHistory monoidalBoundary ∧
          UnaryHistory homObject ∧
            UnaryHistory identity ∧
              UnaryHistory composition ∧
                UnaryHistory transport ∧
                  Cont homObject identity composition ∧
                    Cont transport provenance ledger ∧
                      Cont ledger monoidalBoundary endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  exact packet

end BEDC.Derived.EnrichedCatUp
