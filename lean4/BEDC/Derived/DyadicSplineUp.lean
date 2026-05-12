import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DyadicSplineUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicSplineFiniteCarrier [AskSetup] [PackageSetup]
    (k a l i q r h c p n endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory k ∧ UnaryHistory a ∧ UnaryHistory l ∧ UnaryHistory i ∧
    UnaryHistory q ∧ UnaryHistory r ∧ UnaryHistory h ∧ UnaryHistory c ∧
      UnaryHistory p ∧ UnaryHistory n ∧ UnaryHistory endpoint ∧ Cont k a l ∧
        Cont i q r ∧ Cont h c p ∧ Cont l r endpoint ∧ PkgSig bundle endpoint pkg

theorem DyadicSplineFiniteCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {k a l i q r h c p n endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicSplineFiniteCarrier k a l i q r h c p n endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          DyadicSplineFiniteCarrier k a l i q r h c p n endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          DyadicSplineFiniteCarrier k a l i q r h c p n endpoint bundle pkg ∧
            hsame row endpoint)
        (fun row : BHist =>
          DyadicSplineFiniteCarrier k a l i q r h c p n endpoint bundle pkg ∧
            hsame row endpoint)
        hsame := by
  intro carrier
  constructor
  · constructor
    · exact Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
    · intro row _source
      exact hsame_refl row
    · intro row row' same
      exact hsame_symm same
    · intro row row' row'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro row row' same source
      exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
  · intro row source
    exact source
  · intro row source
    exact source

end BEDC.Derived.DyadicSplineUp
