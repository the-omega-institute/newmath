import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorTerminalConsumerStrictObstruction [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead terminalRead auditBoundary obstruction
      hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead N terminalRead ->
          Cont A G auditBoundary ->
            Cont terminalRead auditBoundary obstruction ->
              PkgSig bundle obstruction pkg ->
                UnaryHistory outputRead ∧ UnaryHistory terminalRead ∧
                  UnaryHistory auditBoundary ∧ UnaryHistory obstruction ∧
                    Cont O A outputRead ∧ Cont outputRead N terminalRead ∧
                      Cont A G auditBoundary ∧ Cont terminalRead auditBoundary obstruction ∧
                        hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle obstruction pkg ∧
                            (Cont obstruction (BHist.e0 hostTail) O -> False) ∧
                              (Cont obstruction (BHist.e1 hostTail) O -> False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputRoute terminalRoute auditRoute obstructionRoute obstructionPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH, unaryC,
      provenanceUnary, unaryG, unaryN, _rootMotive, _branchDescent, _descentAudit,
      transportSame, provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed outputUnary unaryN terminalRoute
  have auditBoundaryUnary : UnaryHistory auditBoundary :=
    unary_cont_closed unaryA unaryG auditRoute
  have obstructionUnary : UnaryHistory obstruction :=
    unary_cont_closed terminalUnary auditBoundaryUnary obstructionRoute
  have outputToObstruction :
      Cont O (append A (append N auditBoundary)) obstruction := by
    cases outputRoute
    cases terminalRoute
    exact obstructionRoute.trans
      ((append_assoc (append O A) N auditBoundary).trans
        (append_assoc O A (append N auditBoundary)))
  have obstructionLeft :
      Cont obstruction (BHist.e0 hostTail) O -> False :=
    fun back =>
      (cont_mutual_extension_right_tail_absurd.left outputToObstruction back)
  have obstructionRight :
      Cont obstruction (BHist.e1 hostTail) O -> False :=
    fun back =>
      (cont_mutual_extension_right_tail_absurd.right outputToObstruction back)
  exact
    ⟨outputUnary, terminalUnary, auditBoundaryUnary, obstructionUnary, outputRoute,
      terminalRoute, auditRoute, obstructionRoute, transportSame, provenancePkg,
      obstructionPkg, obstructionLeft, obstructionRight⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
