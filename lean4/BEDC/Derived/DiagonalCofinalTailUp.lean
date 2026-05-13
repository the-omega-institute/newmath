import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DiagonalCofinalTailUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DiagonalCofinalTailCarrier [AskSetup] [PackageSetup]
    (q s g d r w h c p n : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧
    UnaryHistory r ∧ UnaryHistory w ∧ UnaryHistory h ∧ UnaryHistory c ∧
      UnaryHistory p ∧ UnaryHistory n ∧ Cont q s g ∧ Cont g d r ∧
        Cont w h c ∧ PkgSig bundle p pkg

theorem DiagonalCofinalTailCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {q s g d r w h c p n consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalCofinalTailCarrier q s g d r w h c p n bundle pkg →
      Cont w r consumer →
      PkgSig bundle consumer pkg →
        UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory g ∧ UnaryHistory d ∧
          UnaryHistory r ∧ UnaryHistory w ∧ UnaryHistory h ∧ UnaryHistory c ∧
            UnaryHistory p ∧ UnaryHistory n ∧ UnaryHistory consumer ∧
              Cont q s g ∧ Cont g d r ∧ Cont w h c ∧ Cont w r consumer ∧
                PkgSig bundle p pkg ∧ PkgSig bundle consumer pkg ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row p ∧ UnaryHistory row)
                    (fun row : BHist => hsame row p)
                    (fun row : BHist => hsame row p ∧ PkgSig bundle p pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro carrier consumerRoute consumerPkg
  obtain ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, hUnary, cUnary,
    pUnary, nUnary, qsRoute, gdRoute, whRoute, pPkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed wUnary rUnary consumerRoute
  have sourceP : (fun row : BHist => hsame row p ∧ UnaryHistory row) p := by
    exact And.intro (hsame_refl p) pUnary
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row p ∧ UnaryHistory row)
        (fun row : BHist => hsame row p)
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
          intro row other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact source.left
      ledger_sound := by
        intro _row source
        exact And.intro source.left pPkg
    }
  exact
    ⟨qUnary, sUnary, gUnary, dUnary, rUnary, wUnary, hUnary, cUnary, pUnary,
      nUnary, consumerUnary, qsRoute, gdRoute, whRoute, consumerRoute, pPkg,
      consumerPkg, cert⟩

end BEDC.Derived.DiagonalCofinalTailUp
