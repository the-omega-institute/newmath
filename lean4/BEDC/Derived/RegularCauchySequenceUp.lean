import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchySequenceCarrier [AskSetup] [PackageSetup]
    (f mu w d r g e h c p name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory f ∧ UnaryHistory mu ∧ UnaryHistory w ∧ UnaryHistory d ∧
    UnaryHistory r ∧ UnaryHistory g ∧ UnaryHistory e ∧ UnaryHistory h ∧
      UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory name ∧
        Cont f mu w ∧ Cont w d r ∧ Cont r g e ∧ Cont e h c ∧
          Cont c p name ∧ PkgSig bundle p pkg

theorem RegularCauchySequenceCarrier_window_regularity [AskSetup] [PackageSetup]
    {f mu w d r g e h c p name window consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchySequenceCarrier f mu w d r g e h c p name bundle pkg →
      Cont mu w window →
        Cont window d consumer →
          PkgSig bundle consumer pkg →
            UnaryHistory f ∧ UnaryHistory mu ∧ UnaryHistory w ∧ UnaryHistory d ∧
              UnaryHistory r ∧ UnaryHistory g ∧ UnaryHistory e ∧ UnaryHistory consumer ∧
                Cont mu w window ∧ Cont window d consumer ∧ PkgSig bundle consumer pkg ∧
                  SemanticNameCert
                    (fun row : BHist => hsame row f ∧ UnaryHistory row)
                    (fun row : BHist => hsame row f)
                    (fun row : BHist => hsame row f ∧ PkgSig bundle p pkg)
                    hsame := by
  intro carrier windowRow consumerRow consumerPkg
  have fUnary : UnaryHistory f := carrier.left
  have muUnary : UnaryHistory mu := carrier.right.left
  have wUnary : UnaryHistory w := carrier.right.right.left
  have dUnary : UnaryHistory d := carrier.right.right.right.left
  have rUnary : UnaryHistory r := carrier.right.right.right.right.left
  have gUnary : UnaryHistory g := carrier.right.right.right.right.right.left
  have eUnary : UnaryHistory e := carrier.right.right.right.right.right.right.left
  have pPkg : PkgSig bundle p pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have windowUnary : UnaryHistory window :=
    unary_cont_closed muUnary wUnary windowRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed windowUnary dUnary consumerRow
  have sourceF :
      (fun row : BHist => hsame row f ∧ UnaryHistory row) f := by
    exact ⟨hsame_refl f, fUnary⟩
  have core :
      NameCert
        (fun row : BHist => hsame row f ∧ UnaryHistory row)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro f sourceF
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' same source
        have sameRow' : hsame row' f :=
          hsame_trans (hsame_symm same) source.left
        exact ⟨sameRow', unary_transport source.right same⟩
    }
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row f ∧ UnaryHistory row)
        (fun row : BHist => hsame row f)
        (fun row : BHist => hsame row f ∧ PkgSig bundle p pkg)
        hsame := by
    exact {
      core := core
      pattern_sound := by
        intro row source
        exact source.left
      ledger_sound := by
        intro row source
        exact ⟨source.left, pPkg⟩
    }
  exact
    ⟨fUnary, muUnary, wUnary, dUnary, rUnary, gUnary, eUnary, consumerUnary,
      windowRow, consumerRow, consumerPkg, cert⟩

end BEDC.Derived.RegularCauchySequenceUp
