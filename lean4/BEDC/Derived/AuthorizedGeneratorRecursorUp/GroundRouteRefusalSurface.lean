import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorGroundRouteRefusalSurface [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N groundRead refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont G N groundRead ->
        Cont groundRead A refusalRead ->
          PkgSig bundle refusalRead pkg ->
            UnaryHistory G ∧ UnaryHistory N ∧ UnaryHistory A ∧ UnaryHistory groundRead ∧
              UnaryHistory refusalRead ∧ hsame H (append A C) ∧ Cont G N groundRead ∧
                Cont groundRead A refusalRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier groundRoute refusalRoute refusalPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, _unaryO, unaryA, _unaryH,
      unaryC, unaryP, unaryG, unaryN, _iem, _mbd, _doa, sameTransport, provenancePkg⟩
  have groundUnary : UnaryHistory groundRead :=
    unary_cont_closed unaryG unaryN groundRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed groundUnary unaryA refusalRoute
  exact
    ⟨unaryG, unaryN, unaryA, groundUnary, refusalUnary, sameTransport, groundRoute,
      refusalRoute, provenancePkg, refusalPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
