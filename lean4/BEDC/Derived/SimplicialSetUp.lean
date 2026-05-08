import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.SimplicialSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def SimplicialSetBHistSimplexRowCarrier [AskSetup] [PackageSetup]
    (functor simplex face degeneracy package provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont functor simplex face ∧ Cont simplex functor degeneracy ∧
    PkgSig bundle provenance pkg ∧ Cont package provenance ledger

theorem SimplicialSetBHistSimplexRowCarrier_namecert_obligation_surface
    [AskSetup] [PackageSetup]
    {functor simplex face degeneracy package provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SimplicialSetBHistSimplexRowCarrier functor simplex face degeneracy package provenance
        ledger bundle pkg ->
      SemanticNameCert
          (fun endpoint : BHist =>
            exists face degeneracy package ledger : BHist,
              SimplicialSetBHistSimplexRowCarrier functor endpoint face degeneracy package
                provenance ledger bundle pkg)
          (fun endpoint : BHist =>
            exists face degeneracy package ledger : BHist,
              SimplicialSetBHistSimplexRowCarrier functor endpoint face degeneracy package
                provenance ledger bundle pkg)
          (fun endpoint : BHist =>
            exists face degeneracy package ledger : BHist,
              SimplicialSetBHistSimplexRowCarrier functor endpoint face degeneracy package
                provenance ledger bundle pkg)
          (fun left right : BHist =>
            (exists lf ld lp ll : BHist,
              SimplicialSetBHistSimplexRowCarrier functor left lf ld lp provenance ll
                bundle pkg) ∧
            (exists rf rd rp rl : BHist,
              SimplicialSetBHistSimplexRowCarrier functor right rf rd rp provenance rl
                bundle pkg) ∧
              hsame left right) ∧
        Cont functor simplex face ∧ Cont simplex functor degeneracy ∧
          PkgSig bundle provenance pkg := by
  intro carrier
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          refine Exists.intro simplex ?_
          refine Exists.intro face ?_
          refine Exists.intro degeneracy ?_
          refine Exists.intro package ?_
          exact Exists.intro ledger carrier
        equiv_refl := by
          intro endpoint source
          exact And.intro source (And.intro source (hsame_refl endpoint))
        equiv_symm := by
          intro left right same
          exact And.intro same.right.left
            (And.intro same.left (hsame_symm same.right.right))
        equiv_trans := by
          intro left middle right sameLeftMiddle sameMiddleRight
          exact And.intro sameLeftMiddle.left
            (And.intro sameMiddleRight.right.left
              (hsame_trans sameLeftMiddle.right.right sameMiddleRight.right.right))
        carrier_respects_equiv := by
          intro left right same _source
          exact same.right.left
      }
      pattern_sound := by
        intro endpoint source
        exact source
      ledger_sound := by
        intro endpoint source
        exact source
    }
  · exact And.intro carrier.left (And.intro carrier.right.left carrier.right.right.left)

end BEDC.Derived.SimplicialSetUp
