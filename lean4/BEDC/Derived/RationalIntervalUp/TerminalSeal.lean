import BEDC.Derived.RationalIntervalUp

namespace BEDC.Derived.RationalIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RationalIntervalPacket_normal_form_terminal_seal_compatibility [AskSetup] [PackageSetup]
    {left right order containment transport route provenance name endpoint terminalConsumer
      terminalRead normalSeal terminalSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RationalIntervalPacket left right order containment transport route provenance name endpoint
        bundle pkg ->
      UnaryHistory terminalConsumer ->
        Cont endpoint terminalConsumer terminalRead ->
          Cont endpoint terminalRead normalSeal ->
            Cont normalSeal provenance terminalSeal ->
              PkgSig bundle normalSeal pkg ->
                PkgSig bundle terminalSeal pkg ->
                  UnaryHistory terminalRead ∧ UnaryHistory normalSeal ∧
                    UnaryHistory terminalSeal ∧ hsame normalSeal (append endpoint terminalRead) ∧
                      Cont endpoint terminalConsumer terminalRead ∧
                        Cont endpoint terminalRead normalSeal ∧
                          Cont normalSeal provenance terminalSeal ∧
                            PkgSig bundle normalSeal pkg ∧
                              PkgSig bundle terminalSeal pkg := by
  intro packet terminalConsumerUnary endpointConsumerRead endpointReadSeal sealProvenanceTerminal
    normalSealPkg terminalSealPkg
  obtain ⟨_leftUnary, _rightUnary, _orderUnary, _containmentUnary, _transportUnary,
    _routeUnary, provenanceUnary, _nameUnary, endpointUnary, _orderRow, _containmentRow,
    _provenanceRow, _endpointRow, _endpointPkg⟩ := packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed endpointUnary terminalConsumerUnary endpointConsumerRead
  have normalSealUnary : UnaryHistory normalSeal :=
    unary_cont_closed endpointUnary terminalReadUnary endpointReadSeal
  have terminalSealUnary : UnaryHistory terminalSeal :=
    unary_cont_closed normalSealUnary provenanceUnary sealProvenanceTerminal
  have normalSealAppend : hsame normalSeal (append endpoint terminalRead) :=
    endpointReadSeal
  exact
    ⟨terminalReadUnary, normalSealUnary, terminalSealUnary, normalSealAppend,
      endpointConsumerRead, endpointReadSeal, sealProvenanceTerminal, normalSealPkg,
      terminalSealPkg⟩

end BEDC.Derived.RationalIntervalUp
