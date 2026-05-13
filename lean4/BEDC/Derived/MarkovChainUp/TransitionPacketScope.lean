import BEDC.Derived.MarkovChainUp

namespace BEDC.Derived.MarkovChainUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MarkovChainTransitionCarrier_transition_packet_scope [AskSetup] [PackageSetup]
    {probSource timeLedger randomVarRows lawRows transitionRows contLedger provenance
      endpoint : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MarkovChainTransitionCarrier probSource timeLedger randomVarRows lawRows transitionRows
        contLedger provenance endpoint bundle pkg ->
      UnaryHistory probSource ∧ UnaryHistory timeLedger ∧ UnaryHistory randomVarRows ∧
        UnaryHistory lawRows ∧ UnaryHistory transitionRows ∧ UnaryHistory contLedger ∧
          UnaryHistory provenance ∧ UnaryHistory endpoint ∧
            Cont probSource randomVarRows lawRows ∧
              Cont lawRows transitionRows contLedger ∧
                Cont provenance contLedger endpoint ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.left,
      carrier.right.right.right.right.right.right.right.right.right.right.right⟩

end BEDC.Derived.MarkovChainUp
