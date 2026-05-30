import BEDC.Derived.DedekindMacNeilleCompletionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DedekindMacNeilleCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DedekindMacNeilleCompletionCarrier_cut_closure [AskSetup] [PackageSetup]
    {L U K Q E H C P N lowerUpper realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont L U K ->
      Cont K Q E ->
        Cont E C realSeal ->
          UnaryHistory L ->
            UnaryHistory U ->
              UnaryHistory Q ->
                UnaryHistory C ->
                  PkgSig bundle realSeal pkg ->
                    UnaryHistory K ∧ UnaryHistory E ∧ UnaryHistory realSeal ∧
                      Cont L U K ∧ Cont K Q E ∧ Cont E C realSeal ∧
                        PkgSig bundle realSeal pkg ∧
                          List.Mem
                            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist K)
                            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow
                              (DedekindMacNeilleCompletionUp.mk L U K Q E H C P N)) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro routeLU routeKQ routeEC unaryL unaryU unaryQ unaryC realPkg
  have unaryK : UnaryHistory K := unary_cont_closed unaryL unaryU routeLU
  have unaryE : UnaryHistory E := unary_cont_closed unaryK unaryQ routeKQ
  have unaryReal : UnaryHistory realSeal := unary_cont_closed unaryE unaryC routeEC
  exact
    ⟨unaryK, unaryE, unaryReal, routeLU, routeKQ, routeEC, realPkg,
      by
        simp only [DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow]
        right
        right
        right
        left⟩

end BEDC.Derived.DedekindMacNeilleCompletionUp
