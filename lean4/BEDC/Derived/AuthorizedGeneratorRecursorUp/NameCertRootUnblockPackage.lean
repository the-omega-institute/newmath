import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.Sig

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorNameCertRootUnblockPackage [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A rootRead ->
        PkgSig bundle rootRead pkg ->
          UnaryHistory I ∧ UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory A ∧
            UnaryHistory O ∧ UnaryHistory rootRead ∧ Cont I E M ∧ Cont M B D ∧
              Cont D O A ∧ Cont O A rootRead ∧ hsame H (append A C) ∧
                PkgSig bundle P pkg ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier outputAuditRoot rootPkg
  obtain ⟨unaryI, _unaryE, _unaryM, unaryB, unaryD, unaryO, unaryA, _unaryH, _unaryC,
    _unaryP, _unaryG, _unaryN, contIEM, contMBD, contDOA, sameTransport,
    provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed unaryO unaryA outputAuditRoot
  exact
    ⟨unaryI, unaryB, unaryD, unaryA, unaryO, rootUnary, contIEM, contMBD, contDOA,
      outputAuditRoot, sameTransport, provenancePkg, rootPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
