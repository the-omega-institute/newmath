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

theorem AuthorizedGeneratorRecursorRootOutputNameCertSaturation [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N publicRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O C publicRead ->
        Cont G N boundaryRead ->
          PkgSig bundle publicRead pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
                    hsame row publicRead)
                (fun row : BHist => hsame row publicRead ∧ Cont O C publicRead)
                (fun row : BHist =>
                  hsame row publicRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory publicRead ∧ UnaryHistory boundaryRead ∧
                Cont O C publicRead ∧ Cont G N boundaryRead ∧
                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier outputPublic boundaryRoute publicPkg
  rcases carrier with
    ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, _unaryA, _unaryH,
      unaryC, provenanceUnary, unaryG, unaryN, _signatureMotive, _motiveDescent,
      _descentAudit, _transportSame, provenancePkg⟩
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed unaryO unaryC outputPublic
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed unaryG unaryN boundaryRoute
  have sourcePublic :
      (fun row : BHist =>
        AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
          hsame row publicRead) publicRead := by
    exact ⟨
      ⟨_unaryI, _unaryE, _unaryM, _unaryB, _unaryD, unaryO, _unaryA, _unaryH,
        unaryC, provenanceUnary, unaryG, unaryN, _signatureMotive, _motiveDescent,
        _descentAudit, _transportSame, provenancePkg⟩,
      hsame_refl publicRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ∧
              hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ Cont O C publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
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
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.right, outputPublic⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.right, provenancePkg, publicPkg⟩
    }
  exact ⟨cert, publicUnary, boundaryUnary, outputPublic, boundaryRoute, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
