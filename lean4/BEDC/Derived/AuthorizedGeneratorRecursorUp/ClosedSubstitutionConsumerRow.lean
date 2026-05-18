import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorClosedSubstitutionConsumerRow [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead consumerRead
      lockedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont I E branchRead →
        Cont branchRead D descentRead →
          Cont descentRead O outputRead →
            Cont outputRead C consumerRead →
              Cont consumerRead N lockedRead →
                PkgSig bundle lockedRead pkg →
                  UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                    UnaryHistory outputRead ∧ UnaryHistory consumerRead ∧
                      UnaryHistory lockedRead ∧ Cont I E branchRead ∧
                        Cont branchRead D descentRead ∧
                          Cont descentRead O outputRead ∧
                            Cont outputRead C consumerRead ∧
                              Cont consumerRead N lockedRead ∧ hsame H (append A C) ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle lockedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier rootBranch branchDescent descentOutput outputConsumer consumerLocked lockedPkg
  rcases carrier with
    ⟨unaryI, unaryE, _unaryM, _unaryB, unaryD, unaryO, _unaryA, _unaryH, unaryC,
      _unaryP, _unaryG, unaryN, _rootMotive, _branchDescent, _descentAudit,
      transportSame, packagePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryI unaryE rootBranch
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed branchUnary unaryD branchDescent
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary unaryO descentOutput
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed outputUnary unaryC outputConsumer
  have lockedUnary : UnaryHistory lockedRead :=
    unary_cont_closed consumerUnary unaryN consumerLocked
  exact
    ⟨branchUnary, descentUnary, outputUnary, consumerUnary, lockedUnary, rootBranch,
      branchDescent, descentOutput, outputConsumer, consumerLocked, transportSame,
      packagePkg, lockedPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
