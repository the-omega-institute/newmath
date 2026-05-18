import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootAuthorizationDownstreamSurface [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead consumerRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead C consumerRead ->
          Cont G N boundaryRead ->
            UnaryHistory outputRead ∧ UnaryHistory consumerRead ∧
              UnaryHistory boundaryRead ∧ hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                Cont O A outputRead ∧ Cont outputRead C consumerRead ∧
                  Cont G N boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier outputAudit consumerRoute boundaryRoute
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      unaryC, unaryP, unaryG, unaryN, _iem, _mbd, _doa, sameTransport, pkgSig⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputAudit
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed outputUnary unaryC consumerRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  exact
    ⟨outputUnary, consumerUnary, boundaryUnary, sameTransport, pkgSig, outputAudit,
      consumerRoute, boundaryRoute⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
