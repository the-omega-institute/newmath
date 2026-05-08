import BEDC.Derived.BilinFormUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BilinFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem BilinFormBHistObligationSurface_semantic_name_certificate
    {left right scalar additive endpoint scalarLedger ledger : BHist} :
    BilinFormBHistObligationSurface left right scalar additive endpoint scalarLedger ledger ->
      SemanticNameCert
        (fun h : BHist =>
          exists s l : BHist,
            BilinFormBHistObligationSurface left right scalar additive h s l)
        (fun h : BHist =>
          exists s l : BHist,
            BilinFormBHistObligationSurface left right scalar additive h s l)
        (fun h : BHist =>
          exists s l : BHist,
            BilinFormBHistObligationSurface left right scalar additive h s l)
        (fun a b : BHist =>
          (exists as al : BHist,
            BilinFormBHistObligationSurface left right scalar additive a as al) ∧
            (exists bs bl : BHist,
              BilinFormBHistObligationSurface left right scalar additive b bs bl) ∧
              hsame a b) := by
  intro surface
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (Exists.intro scalarLedger (Exists.intro ledger surface))
      equiv_refl := by
        intro h source
        exact And.intro source (And.intro source (hsame_refl h))
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

end BEDC.Derived.BilinFormUp
