import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorGroundCompilerAuthorizationStrictObstruction
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead boundaryRead strictRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont O A outputRead →
        Cont outputRead G boundaryRead →
          Cont boundaryRead N strictRead →
            PkgSig bundle strictRead pkg →
              UnaryHistory outputRead ∧ UnaryHistory boundaryRead ∧
                UnaryHistory strictRead ∧ Cont O A outputRead ∧
                  Cont outputRead G boundaryRead ∧ Cont boundaryRead N strictRead ∧
                    hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle strictRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier outputAudit outputBoundary boundaryLocal strictPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      _unaryC, _unaryP, unaryG, unaryN, _rootMotive, _branchDescent, _descentAudit,
      transportSame, packagePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputAudit
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed outputUnary unaryG outputBoundary
  have strictUnary : UnaryHistory strictRead :=
    unary_cont_closed boundaryUnary unaryN boundaryLocal
  exact
    ⟨outputUnary, boundaryUnary, strictUnary, outputAudit, outputBoundary, boundaryLocal,
      transportSame, packagePkg, strictPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
