import BEDC.Derived.GroupUp
import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.LieGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem LieGroupSingleton_semantic_name_certificate :
    SemanticNameCert
        (fun h : BHist => GroupSingletonCarrier h ∧ ManifoldSingletonCarrier h)
        (fun h : BHist => GroupSingletonCarrier h ∧ ManifoldSingletonCarrier h)
        (fun h : BHist => GroupSingletonCarrier h ∧ ManifoldSingletonCarrier h)
        (fun h k : BHist =>
          GroupSingletonCarrier h ∧ ManifoldSingletonCarrier h ∧
            GroupSingletonCarrier k ∧ ManifoldSingletonCarrier k ∧ hsame h k) ∧
      (forall {h k product : BHist}, GroupSingletonCarrier h -> GroupSingletonCarrier k ->
        Cont h k product ->
          GroupSingletonCarrier product ∧ ManifoldSingletonCarrier product ∧
            UnaryHistory product) := by
  have emptyCarrier :
      GroupSingletonCarrier BHist.Empty ∧ ManifoldSingletonCarrier BHist.Empty :=
    And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
        equiv_refl := by
          intro h carrier
          exact And.intro carrier.left
            (And.intro carrier.right
              (And.intro carrier.left (And.intro carrier.right (hsame_refl h))))
        equiv_symm := by
          intro h k classified
          exact And.intro classified.right.right.left
            (And.intro classified.right.right.right.left
              (And.intro classified.left
                (And.intro classified.right.left
                  (hsame_symm classified.right.right.right.right))))
        equiv_trans := by
          intro h k r classifiedHK classifiedKR
          exact And.intro classifiedHK.left
            (And.intro classifiedHK.right.left
              (And.intro classifiedKR.right.right.left
                (And.intro classifiedKR.right.right.right.left
                  (hsame_trans classifiedHK.right.right.right.right
                    classifiedKR.right.right.right.right))))
        carrier_respects_equiv := by
          intro h k classified _source
          exact And.intro classified.right.right.left classified.right.right.right.left
      }
      pattern_sound := by
        intro h source
        exact source
      ledger_sound := by
        intro h source
        exact source
    }
  · intro h k product carrierH carrierK productRow
    have productEmpty : hsame product BHist.Empty := by
      exact productRow.trans (append_eq_empty_iff.mpr (And.intro carrierH carrierK))
    exact And.intro productEmpty
      (And.intro productEmpty (unary_transport unary_empty (hsame_symm productEmpty)))

end BEDC.Derived.LieGroupUp
