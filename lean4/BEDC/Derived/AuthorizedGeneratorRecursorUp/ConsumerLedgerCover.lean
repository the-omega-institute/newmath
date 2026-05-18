import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorConsumerLedgerCover [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont branchRead M descentRead ->
          Cont descentRead O outputRead ->
            Cont outputRead N consumerRead ->
              PkgSig bundle consumerRead pkg ->
                UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory O ∧
                  UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                    UnaryHistory outputRead ∧ UnaryHistory consumerRead ∧
                      Cont B D branchRead ∧ Cont branchRead M descentRead ∧
                        Cont descentRead O outputRead ∧ Cont outputRead N consumerRead ∧
                          hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier branchStep descentStep outputStep consumerStep consumerPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, unaryM, unaryB, unaryD, unaryO, _unaryA, _unaryH,
      _unaryC, _unaryP, _unaryG, unaryN, _contIEM, _contMBD, _contDOA,
      transportSame, provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryD branchStep
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed branchUnary unaryM descentStep
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary unaryO outputStep
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed outputUnary unaryN consumerStep
  exact
    ⟨unaryB, unaryD, unaryM, unaryO, branchUnary, descentUnary, outputUnary,
      consumerUnary, branchStep, descentStep, outputStep, consumerStep, transportSame,
      provenancePkg, consumerPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
