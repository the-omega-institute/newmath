import BEDC.Derived.AuthorizedGeneratorRecursorUp.RootBoundaryNonescapeSaturation

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootOutputRouteStrictObstruction
    [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead publicRead boundaryRead
      auditRead obstructionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E branchRead ->
        Cont branchRead D descentRead ->
          Cont descentRead O outputRead ->
            Cont outputRead C publicRead ->
              Cont G N boundaryRead ->
                Cont O A auditRead ->
                  Cont auditRead N obstructionRead ->
                    PkgSig bundle publicRead pkg ->
                      PkgSig bundle obstructionRead pkg ->
                        UnaryHistory publicRead ∧ UnaryHistory boundaryRead ∧
                          UnaryHistory auditRead ∧ UnaryHistory obstructionRead ∧
                            Cont I E branchRead ∧ Cont branchRead D descentRead ∧
                              Cont descentRead O outputRead ∧ Cont outputRead C publicRead ∧
                                Cont G N boundaryRead ∧ Cont O A auditRead ∧
                                  Cont auditRead N obstructionRead ∧ hsame H (append A C) ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg ∧
                                      PkgSig bundle obstructionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig Cont UnaryHistory hsame
  intro carrier branchRoute descentRoute outputRoute publicRoute boundaryRoute auditRoute
    obstructionRoute publicPkg obstructionPkg
  have saturated :
      UnaryHistory publicRead ∧ UnaryHistory boundaryRead ∧ UnaryHistory auditRead ∧
        Cont I E branchRead ∧ Cont branchRead D descentRead ∧
          Cont descentRead O outputRead ∧ Cont outputRead C publicRead ∧
            Cont G N boundaryRead ∧ Cont O A auditRead ∧ hsame H (append A C) ∧
              PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg :=
    AuthorizedGeneratorRecursorRootBoundaryNonescapeSaturation carrier branchRoute
      descentRoute outputRoute publicRoute boundaryRoute auditRoute publicPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, _unaryO, _unaryA, _unaryH,
      _unaryC, _unaryP, _unaryG, localCertUnary, _carrierBranch, _carrierDescent,
      _carrierOutput, _transportSame, _provenancePkg⟩
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed saturated.right.right.left localCertUnary obstructionRoute
  rcases saturated with
    ⟨publicUnary, boundaryUnary, auditUnary, branchRoute', descentRoute', outputRoute',
      publicRoute', boundaryRoute', auditRoute', transportSame, provenancePkg, publicPkg'⟩
  exact
    ⟨publicUnary, boundaryUnary, auditUnary, obstructionUnary, branchRoute', descentRoute',
      outputRoute', publicRoute', boundaryRoute', auditRoute', obstructionRoute, transportSame,
      provenancePkg, publicPkg', obstructionPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
