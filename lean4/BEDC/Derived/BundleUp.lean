import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BundleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def BundleLocalTrivPkg
    (base total projection fiber ledger : BHist)
    (trivRows transitionRows : ProbeBundle BHist) : Prop :=
  Cont base total ledger ∧ InBundle projection trivRows ∧ InBundle fiber transitionRows

theorem BundleLocalTrivPkg_semantic_name_certificate :
    SemanticNameCert
      (fun ledger : BHist =>
        ∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
          BundleLocalTrivPkg base total projection fiber ledger trivRows transitionRows)
      (fun ledger : BHist =>
        ∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
          BundleLocalTrivPkg base total projection fiber ledger trivRows transitionRows)
      (fun ledger : BHist =>
        ∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
          BundleLocalTrivPkg base total projection fiber ledger trivRows transitionRows)
      (fun left right : BHist =>
        (∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
          BundleLocalTrivPkg base total projection fiber left trivRows transitionRows) ∧
        (∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
          BundleLocalTrivPkg base total projection fiber right trivRows transitionRows) ∧
        hsame left right) := by
  let singletonRows : ProbeBundle BHist := ProbeBundle.Bcons BHist.Empty ProbeBundle.Bnil
  let carrier : BHist -> Prop := fun ledger : BHist =>
    ∃ base total projection fiber : BHist, ∃ trivRows transitionRows : ProbeBundle BHist,
      BundleLocalTrivPkg base total projection fiber ledger trivRows transitionRows
  have emptyPkg : BundleLocalTrivPkg BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty singletonRows singletonRows := by
    exact And.intro (cont_left_unit BHist.Empty)
      (And.intro (inBundle_cons_self BHist.Empty ProbeBundle.Bnil)
        (inBundle_cons_self BHist.Empty ProbeBundle.Bnil))
  have emptyCarrier : carrier BHist.Empty :=
    Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (Exists.intro BHist.Empty
            (Exists.intro singletonRows (Exists.intro singletonRows emptyPkg)))))
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
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
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

end BEDC.Derived.BundleUp
