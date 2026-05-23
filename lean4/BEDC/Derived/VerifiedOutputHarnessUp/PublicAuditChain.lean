import BEDC.Derived.VerifiedOutputHarnessUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VerifiedOutputHarnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem VerifiedOutputHarnessCarrier_public_audit_chain [AskSetup] [PackageSetup]
    {I T M Q O C A R H K P N promptModel checked auditRead routeRead replayRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T ->
      UnaryHistory M ->
        UnaryHistory O ->
          UnaryHistory C ->
            UnaryHistory A ->
              UnaryHistory R ->
                UnaryHistory K ->
                  UnaryHistory N ->
                    Cont T M promptModel ->
                      Cont O C checked ->
                        Cont checked A auditRead ->
                          Cont auditRead R routeRead ->
                            Cont routeRead K replayRead ->
                              Cont replayRead N namedRead ->
                                PkgSig bundle namedRead pkg ->
                                  UnaryHistory promptModel ∧
                                    UnaryHistory checked ∧
                                      UnaryHistory auditRead ∧
                                        UnaryHistory routeRead ∧
                                          UnaryHistory replayRead ∧
                                            UnaryHistory namedRead ∧
                                              Cont O C checked ∧
                                                Cont checked A auditRead ∧
                                                  Cont auditRead R routeRead ∧
                                                    Cont routeRead K replayRead ∧
                                                      PkgSig bundle namedRead pkg ∧
                                                        List.Mem
                                                          (verifiedOutputHarnessEncodeBHist O)
                                                          (verifiedOutputHarnessToEventFlow
                                                            (VerifiedOutputHarnessUp.mk
                                                              I T M Q O C A R H K P N)) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro unaryT unaryM unaryO unaryC unaryA unaryR unaryK unaryN
  intro traceModel outputChecked checkedAudit auditRoute routeReplay replayNamed namedPkg
  have promptModelUnary : UnaryHistory promptModel :=
    unary_cont_closed unaryT unaryM traceModel
  have checkedUnary : UnaryHistory checked :=
    unary_cont_closed unaryO unaryC outputChecked
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed checkedUnary unaryA checkedAudit
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed auditUnary unaryR auditRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed routeUnary unaryK routeReplay
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary unaryN replayNamed
  have outputListed :
      List.Mem (verifiedOutputHarnessEncodeBHist O)
        (verifiedOutputHarnessToEventFlow
          (VerifiedOutputHarnessUp.mk I T M Q O C A R H K P N)) := by
    change
      List.Mem (verifiedOutputHarnessEncodeBHist O)
        [[BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist I,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist T,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist M,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist Q,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist O,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist C,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist A,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist R,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist H,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist K,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist P,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist N]
    exact
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _)))))))))
  exact
    ⟨promptModelUnary, checkedUnary, auditUnary, routeUnary, replayUnary, namedUnary,
      outputChecked, checkedAudit, auditRoute, routeReplay, namedPkg, outputListed⟩

end BEDC.Derived.VerifiedOutputHarnessUp
