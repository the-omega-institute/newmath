import BEDC.Derived.DiagonalTailSelectorUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonalTailSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalTailSelectorUp_StdBridge [AskSetup] [PackageSetup]
    {r n mu k w d t s h c p name publicRow sealRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalTailSelectorPublicBudgetSource r n mu k w d t s h c p name publicRow
        bundle pkg →
      Cont t s sealRead →
      Cont publicRow sealRead consumer →
      PkgSig bundle sealRead pkg →
      PkgSig bundle consumer pkg →
        SemanticNameCert
            (fun row : BHist => hsame row p ∧ UnaryHistory row)
            (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
            (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
            hsame ∧
          UnaryHistory publicRow ∧ UnaryHistory sealRead ∧ UnaryHistory consumer ∧
            Cont p name publicRow ∧ Cont t s sealRead ∧
              Cont publicRow sealRead consumer ∧ PkgSig bundle p pkg ∧
                PkgSig bundle publicRow pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro source sealRoute consumerRoute _sealPkg _consumerPkg
  obtain ⟨carrier, publicRoute, publicPkg⟩ := source
  obtain ⟨_rUnary, _nUnary, _muUnary, _kUnary, _wUnary, _dUnary, tUnary, sUnary,
    _hUnary, _cUnary, pUnary, nameUnary, _nMuK, _kWD, pPkg⟩ := carrier
  have publicUnary : UnaryHistory publicRow :=
    unary_cont_closed pUnary nameUnary publicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tUnary sUnary sealRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed publicUnary sealUnary consumerRoute
  have sourceP : (fun row : BHist => hsame row p ∧ UnaryHistory row) p := by
    exact And.intro (hsame_refl p) pUnary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row p ∧ UnaryHistory row)
        (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
        (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro p sourceP
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
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact And.intro source.left pPkg
      ledger_sound := by
        intro _row source
        exact And.intro source.left pPkg
    }
  exact
    ⟨cert, publicUnary, sealUnary, consumerUnary, publicRoute, sealRoute,
      consumerRoute, pPkg, publicPkg⟩

end BEDC.Derived.DiagonalTailSelectorUp
