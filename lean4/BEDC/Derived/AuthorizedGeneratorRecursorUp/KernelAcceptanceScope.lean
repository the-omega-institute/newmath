import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorKernelAcceptanceScope [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N kernelRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont G N kernelRead ->
        Cont O A outputRead ->
          PkgSig bundle kernelRead pkg ->
            UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
              UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory G ∧
                UnaryHistory N ∧ UnaryHistory kernelRead ∧ UnaryHistory outputRead ∧
                  Cont I E M ∧ Cont M B D ∧ Cont D O A ∧ Cont G N kernelRead ∧
                    Cont O A outputRead ∧ hsame H (append A C) ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle kernelRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier kernelRoute outputRoute kernelPkg
  obtain ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH,
    _unaryC, _unaryP, unaryG, unaryN, routeIEM, routeMBD, routeDOA,
    transportSame, provenancePkg⟩ := carrier
  have kernelReadUnary : UnaryHistory kernelRead :=
    unary_cont_closed unaryG unaryN kernelRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  exact
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryG, unaryN,
      kernelReadUnary, outputReadUnary, routeIEM, routeMBD, routeDOA, kernelRoute,
      outputRoute, transportSame, provenancePkg, kernelPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
