import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootSignatureTotality [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg →
      Cont A C rootRead →
        PkgSig bundle rootRead pkg →
          UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
            UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧
              UnaryHistory rootRead ∧ Cont I E M ∧ Cont M B D ∧ Cont D O A ∧
                Cont A C rootRead ∧ hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier rootCont rootPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, unaryC,
      unaryP, _unaryG, _unaryN, contIEM, contMBD, contDOA, sameTransport,
      provenancePkg⟩
  have rootUnary : UnaryHistory rootRead := unary_cont_closed unaryA unaryC rootCont
  exact
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, rootUnary, contIEM,
      contMBD, contDOA, rootCont, sameTransport, provenancePkg, rootPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
