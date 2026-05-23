import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorDescentOutputLock [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N descentOutputRead lockedOutputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont D O descentOutputRead ->
        Cont descentOutputRead N lockedOutputRead ->
          PkgSig bundle lockedOutputRead pkg ->
            UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory descentOutputRead ∧
              UnaryHistory lockedOutputRead ∧ Cont D O descentOutputRead ∧
                Cont descentOutputRead N lockedOutputRead ∧ Cont M B D ∧
                  Cont D O A ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle lockedOutputRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier descentOutputRoute lockedOutputRoute lockedOutputPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, unaryD, unaryO, _unaryA, _unaryH,
      _unaryC, carrierPkg, _unaryG, unaryN, _carrierBranch, carrierDescent,
      carrierOutput, _transportSame, provenancePkg⟩
  have descentOutputUnary : UnaryHistory descentOutputRead :=
    unary_cont_closed unaryD unaryO descentOutputRoute
  have lockedOutputUnary : UnaryHistory lockedOutputRead :=
    unary_cont_closed descentOutputUnary unaryN lockedOutputRoute
  exact
    ⟨unaryD, unaryO, descentOutputUnary, lockedOutputUnary, descentOutputRoute,
      lockedOutputRoute, carrierDescent, carrierOutput, provenancePkg, lockedOutputPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
