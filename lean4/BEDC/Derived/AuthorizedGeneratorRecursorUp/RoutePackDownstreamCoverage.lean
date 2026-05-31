import BEDC.Derived.AuthorizedGeneratorRecursorUp.RoutePackExactness

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRoutePackDownstreamCoverage [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead publicRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E branchRead ->
        Cont branchRead D descentRead ->
          Cont descentRead O outputRead ->
            Cont outputRead C publicRead ->
              Cont G N boundaryRead ->
                PkgSig bundle publicRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row publicRead ∧ Cont I E branchRead ∧
                          Cont branchRead D descentRead ∧ Cont descentRead O outputRead ∧
                            Cont outputRead C row ∧ Cont G N boundaryRead)
                      (fun row : BHist =>
                        hsame row publicRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle publicRead pkg)
                      hsame ∧
                    UnaryHistory branchRead ∧ UnaryHistory descentRead ∧
                      UnaryHistory outputRead ∧ UnaryHistory publicRead ∧
                        hsame H (append A C) ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier branchRoute descentRoute outputRoute publicRoute boundaryRoute publicPkg
  have routeCert :=
    AuthorizedGeneratorRecursorRoutePackExactness carrier branchRoute descentRoute outputRoute
      publicRoute boundaryRoute publicPkg
  rcases carrier with
    ⟨unaryI, unaryE, _unaryM, _unaryB, unaryD, unaryO, _unaryA, _unaryH,
      unaryC, _unaryP, _unaryG, _unaryN, _rootCarrier, _descentCarrier,
      _outputCarrier, transportSame, provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryI unaryE branchRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed branchUnary unaryD descentRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary unaryO outputRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed outputUnary unaryC publicRoute
  exact ⟨routeCert, branchUnary, descentUnary, outputUnary, publicUnary, transportSame,
    provenancePkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
