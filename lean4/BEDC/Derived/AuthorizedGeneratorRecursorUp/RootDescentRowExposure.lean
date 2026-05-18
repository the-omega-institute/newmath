import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootDescentRowExposure [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N motiveRead descentRead outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont M B motiveRead ->
        Cont motiveRead D descentRead ->
          Cont D O outputRead ->
            PkgSig bundle outputRead pkg ->
              UnaryHistory D ∧ UnaryHistory motiveRead ∧ UnaryHistory descentRead ∧
                UnaryHistory outputRead ∧ Cont I E M ∧ Cont M B motiveRead ∧
                  Cont motiveRead D descentRead ∧ Cont D O outputRead ∧
                    hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle outputRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier motiveRoute descentRoute outputRoute outputPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, unaryM, unaryB, unaryD, unaryO, _unaryA, _unaryH, _unaryC,
      _unaryP, _unaryG, _unaryN, rootRoute, _motiveDescent, _descentAudit,
      transportSame, provenancePkg⟩
  have motiveReadUnary : UnaryHistory motiveRead :=
    unary_cont_closed unaryM unaryB motiveRoute
  have descentReadUnary : UnaryHistory descentRead :=
    unary_cont_closed motiveReadUnary unaryD descentRoute
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryD unaryO outputRoute
  exact
    ⟨unaryD, motiveReadUnary, descentReadUnary, outputReadUnary, rootRoute,
      motiveRoute, descentRoute, outputRoute, transportSame, provenancePkg, outputPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
