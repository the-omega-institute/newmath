import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolePlacementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PolePlacementSourcePacket [AskSetup] [PackageSetup]
    (state input transition inputMatrix gain feedbackProduct closedLoop target comparison
      provenance boundary : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
    UnaryHistory inputMatrix ∧ UnaryHistory gain ∧ UnaryHistory target ∧
      UnaryHistory boundary ∧ Cont inputMatrix gain feedbackProduct ∧
        Cont transition feedbackProduct closedLoop ∧ Cont closedLoop target comparison ∧
          Cont comparison boundary provenance ∧ PkgSig bundle provenance pkg

def PolePlacementCarrier [AskSetup] [PackageSetup]
    (state input transition inputMatrix gain closedLoop target comparison transport routes
      provenance boundary : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
    UnaryHistory inputMatrix ∧ UnaryHistory gain ∧ UnaryHistory target ∧
      UnaryHistory provenance ∧ UnaryHistory boundary ∧ Cont transition gain closedLoop ∧
        Cont closedLoop target comparison ∧ Cont comparison transport routes ∧
          PkgSig bundle provenance pkg

theorem PolePlacementSourcePacket_closed_loop_ledger [AskSetup] [PackageSetup]
    {state input transition inputMatrix gain feedbackProduct closedLoop target comparison
      provenance boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolePlacementSourcePacket state input transition inputMatrix gain feedbackProduct closedLoop
        target comparison provenance boundary bundle pkg ->
      UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
        UnaryHistory inputMatrix ∧ UnaryHistory gain ∧ UnaryHistory feedbackProduct ∧
          UnaryHistory closedLoop ∧ UnaryHistory target ∧ UnaryHistory comparison ∧
            Cont inputMatrix gain feedbackProduct ∧ Cont transition feedbackProduct closedLoop ∧
              Cont closedLoop target comparison ∧ PkgSig bundle provenance pkg := by
  intro packet
  obtain ⟨stateUnary, inputUnary, transitionUnary, inputMatrixUnary, gainUnary,
    targetUnary, _boundaryUnary, feedbackRow, closedLoopRow, comparisonRow,
    _provenanceRow, provenanceSig⟩ := packet
  have feedbackUnary : UnaryHistory feedbackProduct :=
    unary_cont_closed inputMatrixUnary gainUnary feedbackRow
  have closedLoopUnary : UnaryHistory closedLoop :=
    unary_cont_closed transitionUnary feedbackUnary closedLoopRow
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed closedLoopUnary targetUnary comparisonRow
  exact
    ⟨stateUnary, inputUnary, transitionUnary, inputMatrixUnary, gainUnary,
      feedbackUnary, closedLoopUnary, targetUnary, comparisonUnary, feedbackRow,
      closedLoopRow, comparisonRow, provenanceSig⟩

theorem PolePlacementCarrier_closed_loop_ledger [AskSetup] [PackageSetup]
    {state input transition inputMatrix gain closedLoop target comparison transport routes
      provenance boundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolePlacementCarrier state input transition inputMatrix gain closedLoop target comparison
        transport routes provenance boundary bundle pkg ->
      UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
        UnaryHistory inputMatrix ∧ UnaryHistory gain ∧ UnaryHistory closedLoop ∧
          UnaryHistory target ∧ UnaryHistory comparison ∧ UnaryHistory provenance ∧
            Cont transition gain closedLoop ∧ Cont closedLoop target comparison ∧
              PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨stateUnary, inputUnary, transitionUnary, inputMatrixUnary, gainUnary, targetUnary,
    provenanceUnary, _boundaryUnary, closedLoopRoute, comparisonRoute, _routesRoute,
    provenancePkg⟩ := carrier
  have closedLoopUnary : UnaryHistory closedLoop :=
    unary_cont_closed transitionUnary gainUnary closedLoopRoute
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed closedLoopUnary targetUnary comparisonRoute
  exact
    ⟨stateUnary, inputUnary, transitionUnary, inputMatrixUnary, gainUnary, closedLoopUnary,
      targetUnary, comparisonUnary, provenanceUnary, closedLoopRoute, comparisonRoute,
      provenancePkg⟩

theorem PolePlacementSourcePacket_consumer_boundary [AskSetup] [PackageSetup]
    {state input transition inputMatrix gain feedbackProduct closedLoop target comparison
      provenance boundary consumerRead consumerExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolePlacementSourcePacket state input transition inputMatrix gain feedbackProduct closedLoop
        target comparison provenance boundary bundle pkg ->
      Cont comparison boundary consumerRead ->
        Cont consumerRead provenance consumerExport ->
          PkgSig bundle consumerExport pkg ->
            UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
              UnaryHistory inputMatrix ∧ UnaryHistory gain ∧ UnaryHistory closedLoop ∧
                UnaryHistory target ∧ UnaryHistory comparison ∧ UnaryHistory consumerRead ∧
                  UnaryHistory consumerExport ∧ Cont inputMatrix gain feedbackProduct ∧
                    Cont transition feedbackProduct closedLoop ∧
                      Cont closedLoop target comparison ∧
                        Cont comparison boundary consumerRead ∧
                          Cont consumerRead provenance consumerExport ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle consumerExport pkg := by
  intro packet consumerReadRow consumerExportRow consumerExportPkg
  obtain ⟨stateUnary, inputUnary, transitionUnary, inputMatrixUnary, gainUnary, targetUnary,
    boundaryUnary, feedbackRow, closedLoopRow, comparisonRow, provenanceRow,
    provenancePkg⟩ := packet
  have feedbackUnary : UnaryHistory feedbackProduct :=
    unary_cont_closed inputMatrixUnary gainUnary feedbackRow
  have closedLoopUnary : UnaryHistory closedLoop :=
    unary_cont_closed transitionUnary feedbackUnary closedLoopRow
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed closedLoopUnary targetUnary comparisonRow
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed comparisonUnary boundaryUnary provenanceRow
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed comparisonUnary boundaryUnary consumerReadRow
  have consumerExportUnary : UnaryHistory consumerExport :=
    unary_cont_closed consumerReadUnary provenanceUnary consumerExportRow
  exact
    ⟨stateUnary, inputUnary, transitionUnary, inputMatrixUnary, gainUnary, closedLoopUnary,
      targetUnary, comparisonUnary, consumerReadUnary, consumerExportUnary, feedbackRow,
      closedLoopRow, comparisonRow, consumerReadRow, consumerExportRow, provenancePkg,
      consumerExportPkg⟩

end BEDC.Derived.PolePlacementUp
