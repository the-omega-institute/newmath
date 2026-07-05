import BEDC.Derived.UpperHemicontinuityUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UpperHemicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpperHemicontinuityCarrier_compact_valued_correspondence_handoff
    [AskSetup] [PackageSetup]
    {X Y G K R V O H C P N graphRead compactRead optimizeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier :
      UpperHemicontinuityCarrier_namecert_obligations_carrier X Y G K R V O H C P N
        bundle pkg)
    (graphUnary : UnaryHistory G) (compactUnary : UnaryHistory K)
    (readbackUnary : UnaryHistory R) (dependencyUnary : UnaryHistory V)
    (optimizationUnary : UnaryHistory O) (replayUnary : UnaryHistory C)
    (graphRoute : Cont G K graphRead) (compactRoute : Cont R V compactRead)
    (optimizationRoute : Cont O C optimizeRead) :
    UnaryHistory graphRead ∧ UnaryHistory compactRead ∧ UnaryHistory optimizeRead ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: UpperHemicontinuityUp BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed graphUnary compactUnary graphRoute
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed readbackUnary dependencyUnary compactRoute
  have optimizeReadUnary : UnaryHistory optimizeRead :=
    unary_cont_closed optimizationUnary replayUnary optimizationRoute
  exact
    ⟨graphReadUnary, compactReadUnary, optimizeReadUnary, carrier.right.left,
      carrier.right.right⟩

theorem UpperHemicontinuityCarrier_graph_window_compact_value_stability
    [AskSetup] [PackageSetup]
    {X Y G K R V O H C P N graphRead compactRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    (carrier :
      UpperHemicontinuityCarrier_namecert_obligations_carrier X Y G K R V O H C P N
        bundle pkg)
    (graphUnary : UnaryHistory G) (compactUnary : UnaryHistory K)
    (readbackUnary : UnaryHistory R) (dependencyUnary : UnaryHistory V)
    (replayUnary : UnaryHistory C)
    (graphRoute : Cont G K graphRead) (compactRoute : Cont graphRead R compactRead)
    (consumerRoute : Cont compactRead V consumerRead) :
    UnaryHistory graphRead ∧ UnaryHistory compactRead ∧ UnaryHistory consumerRead ∧
      PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: UpperHemicontinuityUp BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  have graphReadUnary : UnaryHistory graphRead :=
    unary_cont_closed graphUnary compactUnary graphRoute
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed graphReadUnary readbackUnary compactRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed compactReadUnary dependencyUnary consumerRoute
  exact
    ⟨graphReadUnary, compactReadUnary, consumerReadUnary, carrier.right.left,
      carrier.right.right⟩

end BEDC.Derived.UpperHemicontinuityUp
