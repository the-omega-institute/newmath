import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootAuthorizationBridgeDeterminacy
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead consumerRead boundaryRead streamRead regSeqRead
      realRead handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O A outputRead →
        Cont outputRead C consumerRead →
          Cont G N boundaryRead →
            Cont O A streamRead →
              Cont streamRead C regSeqRead →
                Cont regSeqRead G realRead →
                  Cont realRead N handoff →
                    PkgSig bundle handoff pkg →
                      UnaryHistory outputRead ∧ UnaryHistory consumerRead ∧
                        UnaryHistory boundaryRead ∧ UnaryHistory streamRead ∧
                          UnaryHistory regSeqRead ∧ UnaryHistory realRead ∧
                            UnaryHistory handoff ∧ hsame H (append A C) ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAudit outputConsumer boundaryRoute streamRoute regSeqRoute realRoute
    handoffRoute handoffPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      unaryC, _unaryP, unaryG, unaryN, _signatureEliminatorMotive,
      _motiveBranchDescent, _descentOutputAudit, transportSame, provenancePkg⟩
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputAudit
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed outputReadUnary unaryC outputConsumer
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed unaryO unaryA streamRoute
  have regSeqReadUnary : UnaryHistory regSeqRead :=
    unary_cont_closed streamReadUnary unaryC regSeqRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regSeqReadUnary unaryG realRoute
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed realReadUnary unaryN handoffRoute
  exact
    ⟨outputReadUnary, consumerReadUnary, boundaryReadUnary, streamReadUnary, regSeqReadUnary,
      realReadUnary, handoffUnary, transportSame, provenancePkg, handoffPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
