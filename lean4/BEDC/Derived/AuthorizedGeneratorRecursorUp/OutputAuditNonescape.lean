import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier
import BEDC.FKernel.NameCert
import BEDC.FKernel.Sig

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorOutputAuditNonescape [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N outputRead boundaryRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O A outputRead ->
        Cont outputRead G boundaryRead ->
          Cont boundaryRead N publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row O ∧
                      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg)
                  (fun row : BHist =>
                    hsame row O ∧ Cont O A outputRead ∧ Cont outputRead G boundaryRead ∧
                      Cont boundaryRead N publicRead)
                  (fun row : BHist =>
                    hsame row O ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
                  hsame ∧
                UnaryHistory outputRead ∧ UnaryHistory boundaryRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier outputRoute boundaryRoute publicRoute publicPkg
  rcases carrier with
    ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
      provenanceUnary, unaryG, unaryN, carrierBranch, carrierDescent, carrierOutput,
      transportSame, provenancePkg⟩
  have outputUnary : UnaryHistory outputRead :=
    unary_cont_closed unaryO unaryA outputRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed outputUnary unaryG boundaryRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed boundaryUnary unaryN publicRoute
  have carrierWitness :
      AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg := by
    exact
      ⟨unaryI, unaryE, unaryM, unaryB, unaryD, unaryO, unaryA, unaryH, unaryC,
        provenanceUnary, unaryG, unaryN, carrierBranch, carrierDescent, carrierOutput,
        transportSame, provenancePkg⟩
  have sourceOutput :
      (fun row : BHist =>
        hsame row O ∧
          AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg) O := by
    exact ⟨hsame_refl O, carrierWitness⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row O ∧
              AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg)
          (fun row : BHist =>
            hsame row O ∧ Cont O A outputRead ∧ Cont outputRead G boundaryRead ∧
              Cont boundaryRead N publicRead)
          (fun row : BHist =>
            hsame row O ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro O sourceOutput
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, outputRoute, boundaryRoute, publicRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg, publicPkg⟩
    }
  exact ⟨cert, outputUnary, boundaryUnary, publicUnary⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
