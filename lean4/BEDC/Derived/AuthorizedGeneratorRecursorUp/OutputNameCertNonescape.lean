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

theorem AuthorizedGeneratorRecursor_output_namecert_nonescape [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead namedRead boundaryRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead N namedRead ->
          Cont G N boundaryRead ->
            Cont boundaryRead namedRead publicRead ->
              PkgSig bundle publicRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row publicRead ∧ Cont O A outputRead ∧
                        Cont outputRead N namedRead ∧ Cont G N boundaryRead ∧
                          Cont boundaryRead namedRead publicRead)
                    (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                    hsame ∧ UnaryHistory publicRead ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier outputRoute namedRoute boundaryRoute publicRoute publicPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, unaryA, _unaryH,
      _unaryC, _unaryP, unaryG, unaryN, _contIEM, _contMBD, _contDOA,
      _transportAppend, _provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed outputUnary unaryN namedRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed boundaryUnary namedUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont O A outputRead ∧
              Cont outputRead N namedRead ∧ Cont G N boundaryRead ∧
                Cont boundaryRead namedRead publicRead)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro publicRead sourcePublic
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
        exact ⟨source.left, outputRoute, namedRoute, boundaryRoute, publicRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, publicPkg⟩
    }
  exact ⟨cert, publicUnary, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
