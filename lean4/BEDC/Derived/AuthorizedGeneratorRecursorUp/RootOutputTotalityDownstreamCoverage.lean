import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorRootOutputTotalityDownstreamCoverage [AskSetup]
    [PackageSetup]
    {I E M B D O A H C P G N branchRead descentRead outputRead publicRead auditRead
      boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont I E branchRead ->
        Cont branchRead D descentRead ->
          Cont descentRead O outputRead ->
            Cont outputRead C publicRead ->
              Cont publicRead A auditRead ->
                Cont G N boundaryRead ->
                  PkgSig bundle publicRead pkg ->
                    PkgSig bundle auditRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row N ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row N ∧ Cont I E branchRead ∧
                              Cont branchRead D descentRead ∧
                                Cont descentRead O outputRead ∧
                                  Cont outputRead C publicRead ∧
                                    Cont publicRead A auditRead ∧
                                      Cont G N boundaryRead)
                          (fun row : BHist =>
                            hsame row N ∧ PkgSig bundle publicRead pkg ∧
                              PkgSig bundle auditRead pkg)
                          hsame ∧ UnaryHistory auditRead ∧ UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier branchRoute descentRoute outputRoute publicRoute auditRoute boundaryRoute
    publicPkg auditPkg
  rcases carrier with
    ⟨unaryI, unaryE, _unaryM, _unaryB, unaryD, unaryO, unaryA, _unaryH, unaryC,
      _unaryP, unaryG, unaryN, _carrierBranch, _carrierDescent, _carrierOutput,
      _transportSame, _provenancePkg⟩
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed unaryI unaryE branchRoute
  have descentUnary : UnaryHistory descentRead :=
    unary_cont_closed branchUnary unaryD descentRoute
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed descentUnary unaryO outputRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed outputUnary unaryC publicRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed publicUnary unaryA auditRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have sourceN : (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row N ∧ Cont I E branchRead ∧ Cont branchRead D descentRead ∧
              Cont descentRead O outputRead ∧ Cont outputRead C publicRead ∧
                Cont publicRead A auditRead ∧ Cont G N boundaryRead)
          (fun row : BHist =>
            hsame row N ∧ PkgSig bundle publicRead pkg ∧ PkgSig bundle auditRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N sourceN
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, branchRoute, descentRoute, outputRoute, publicRoute, auditRoute,
            boundaryRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, publicPkg, auditPkg⟩
    }
  exact ⟨cert, auditUnary, boundaryUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
