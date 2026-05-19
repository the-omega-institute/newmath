import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorBranchOutputClosureRow [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N sigRead branchRead publicOutput : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E sigRead ->
        Cont sigRead B branchRead ->
          Cont branchRead O publicOutput ->
            PkgSig bundle publicOutput pkg ->
              UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
                UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory sigRead ∧
                  UnaryHistory branchRead ∧ UnaryHistory publicOutput ∧ Cont I E M ∧
                    Cont M B D ∧ Cont D O A ∧ Cont I E sigRead ∧
                      Cont sigRead B branchRead ∧ Cont branchRead O publicOutput ∧
                        hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle publicOutput pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame
  intro carrier sigRoute branchRoute publicRoute publicPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, _unaryA, _transportUnary,
      _continuationUnary, _provenanceUnary, _boundaryUnary, _localUnary, contIEM,
      contMBD, contDOA, sameTransport, provenancePkg⟩
  have sigUnary : UnaryHistory sigRead :=
    unary_cont_closed unaryI unaryE sigRoute
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed sigUnary unaryB branchRoute
  have publicUnary : UnaryHistory publicOutput :=
    unary_cont_closed branchUnary unaryO publicRoute
  exact
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, sigUnary, branchUnary,
      publicUnary, contIEM, contMBD, contDOA, sigRoute, branchRoute, publicRoute,
      sameTransport, provenancePkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
