import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ManifoldAtlasPackage_semanticNameCert :
    SemanticNameCert
      (fun h : BHist =>
        exists base index domain chart : BHist,
          ManifoldAtlasPackage base index domain chart h)
      (fun h : BHist =>
        exists base index domain chart : BHist,
          ManifoldAtlasPackage base index domain chart h)
      (fun h : BHist =>
        exists base index domain chart : BHist,
          ManifoldAtlasPackage base index domain chart h)
      (fun h k : BHist =>
        (exists base index domain chart : BHist,
          ManifoldAtlasPackage base index domain chart h) ∧
        (exists base index domain chart : BHist,
          ManifoldAtlasPackage base index domain chart k) ∧
        hsame h k) := by
  let AtlasCarrier :=
    fun h : BHist =>
      exists base index domain chart : BHist,
        ManifoldAtlasPackage base index domain chart h
  have emptyPackage : AtlasCarrier BHist.Empty := by
    exact Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (Exists.intro BHist.Empty
            (And.intro unary_empty
              (And.intro unary_empty
                (And.intro unary_empty
                  (And.intro unary_empty
                    (And.intro unary_empty
                      (And.intro (cont_left_unit BHist.Empty)
                        (cont_left_unit BHist.Empty))))))))))
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyPackage
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro h k classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro h k r classifiedHK classifiedKR
        exact And.intro classifiedHK.left
          (And.intro classifiedKR.right.left
            (hsame_trans classifiedHK.right.right classifiedKR.right.right))
      carrier_respects_equiv := by
        intro h k classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro h source
      exact source
    ledger_sound := by
      intro h source
      exact source
  }

end BEDC.Derived.ManifoldUp
