import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorClosedSubstitutionAdmission [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead substRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont B D branchRead ->
        Cont branchRead A descentRead ->
          Cont descentRead G substRead ->
            PkgSig bundle substRead pkg ->
              UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory A ∧ UnaryHistory G ∧
                UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                  UnaryHistory substRead ∧ Cont B D branchRead ∧
                    Cont branchRead A descentRead ∧ Cont descentRead G substRead ∧
                      hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle substRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier branchStep descentStep substStep substPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, unaryB, unaryD, _unaryO, unaryA, _unaryH,
      _unaryC, _unaryP, unaryG, _unaryN, _contIEM, _contMBD, _contDOA,
      transportSame, provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryB unaryD branchStep
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed branchUnary unaryA descentStep
  have substUnary : UnaryHistory substRead :=
    unary_cont_closed descentUnary unaryG substStep
  exact
    ⟨unaryB, unaryD, unaryA, unaryG, branchUnary, descentUnary, substUnary,
      branchStep, descentStep, substStep, transportSame, provenancePkg, substPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
