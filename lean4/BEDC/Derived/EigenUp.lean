import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.Derived.LinearMapUp
import BEDC.Derived.CommRingUp
import BEDC.Derived.DeterminantUp

namespace BEDC.Derived.EigenUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.LinearMapUp
open BEDC.Derived.CommRingUp
open BEDC.Derived.DeterminantUp

def EigenComponentSingletonCarrier (f lam v pair : BHist) : Prop :=
  LinearMapSingletonCarrier f ∧ CommRingSingletonCarrier lam ∧
    LinearMapSingletonCarrier v ∧ Cont lam v pair

theorem EigenSingletonCarrier_pair_empty_iff {f lam v pair : BHist} :
    EigenComponentSingletonCarrier f lam v pair ↔
      LinearMapSingletonCarrier f ∧ CommRingSingletonCarrier lam ∧
        LinearMapSingletonCarrier v ∧ hsame pair BHist.Empty := by
  constructor
  · intro carrier
    cases carrier with
    | intro fCarrier rest =>
        cases rest with
        | intro lamCarrier rest =>
            cases rest with
            | intro vCarrier contPair =>
                have pairEmpty : hsame pair BHist.Empty := by
                  have appendEmpty : hsame (append lam v) BHist.Empty :=
                    append_eq_empty_iff.mpr (And.intro lamCarrier vCarrier)
                  exact hsame_trans contPair appendEmpty
                exact And.intro fCarrier
                  (And.intro lamCarrier (And.intro vCarrier pairEmpty))
  · intro carrier
    cases carrier with
    | intro fCarrier rest =>
        cases rest with
        | intro lamCarrier rest =>
            cases rest with
            | intro vCarrier pairEmpty =>
                have appendEmpty : hsame (append lam v) BHist.Empty :=
                  append_eq_empty_iff.mpr (And.intro lamCarrier vCarrier)
                have contPair : Cont lam v pair :=
                  cont_intro (pairEmpty.trans appendEmpty.symm)
                exact And.intro fCarrier
                  (And.intro lamCarrier (And.intro vCarrier contPair))

def EigenSingletonCarrier (pair : BHist) : Prop :=
  ∃ map scalar vector : BHist,
    LinearMapSingletonCarrier map ∧
      DeterminantSingletonCarrier scalar ∧
        LinearMapSingletonCarrier vector ∧ Cont map (append scalar vector) pair

theorem EigenSingletonCarrier_cont_result_transport {map scalar vector pair pair' : BHist} :
    LinearMapSingletonCarrier map ->
      DeterminantSingletonCarrier scalar ->
        LinearMapSingletonCarrier vector ->
          Cont map (append scalar vector) pair -> hsame pair pair' ->
            EigenSingletonCarrier pair' := by
  intro mapCarrier scalarCarrier vectorCarrier contPair samePair
  exact Exists.intro map
    (Exists.intro scalar
      (Exists.intro vector
        (And.intro mapCarrier
          (And.intro scalarCarrier
            (And.intro vectorCarrier (cont_result_hsame_transport contPair samePair))))))

theorem EigenComponentSingletonCarrier_singleton_append {map scalar vector pair : BHist} :
    EigenComponentSingletonCarrier map scalar vector pair ->
      DeterminantSingletonCarrier scalar -> EigenSingletonCarrier (append map pair) := by
  intro componentCarrier scalarCarrier
  cases componentCarrier with
  | intro mapCarrier rest =>
      cases rest with
      | intro _scalarCommCarrier rest =>
          cases rest with
          | intro vectorCarrier scalarVectorCont =>
              exact Exists.intro map
                (Exists.intro scalar
                  (Exists.intro vector
                    (And.intro mapCarrier
                      (And.intro scalarCarrier
                        (And.intro vectorCarrier
                          (cont_intro (congrArg (append map) scalarVectorCont)))))))

theorem EigenSingletonCarrier_empty_iff {pair : BHist} :
    EigenSingletonCarrier pair ↔ hsame pair BHist.Empty := by
  constructor
  · intro carrier
    cases carrier with
    | intro map carrier =>
        cases carrier with
        | intro scalar carrier =>
            cases carrier with
            | intro vector carrier =>
                cases carrier with
                | intro mapCarrier rest =>
                    cases rest with
                    | intro scalarCarrier rest =>
                        cases rest with
                        | intro vectorCarrier contPair =>
                            have scalarVectorEmpty :
                                hsame (append scalar vector) BHist.Empty :=
                              append_eq_empty_iff.mpr (And.intro scalarCarrier vectorCarrier)
                            have resultEmpty :
                                hsame (append map (append scalar vector)) BHist.Empty :=
                              append_eq_empty_iff.mpr (And.intro mapCarrier scalarVectorEmpty)
                            exact hsame_trans contPair resultEmpty
  · intro pairEmpty
    exact Exists.intro BHist.Empty
      (Exists.intro BHist.Empty
        (Exists.intro BHist.Empty
          (And.intro (hsame_refl BHist.Empty)
            (And.intro (hsame_refl BHist.Empty)
              (And.intro (hsame_refl BHist.Empty) (cont_intro pairEmpty))))))

theorem EigenSingletonCarrier_append_context_empty_iff {L R h : BHist} :
    EigenSingletonCarrier (append L (append h R)) ↔
      hsame L BHist.Empty ∧ EigenSingletonCarrier h ∧ hsame R BHist.Empty := by
  constructor
  · intro carrier
    have contextualEmpty : hsame (append L (append h R)) BHist.Empty :=
      EigenSingletonCarrier_empty_iff.mp carrier
    have outerSplit := append_eq_empty_iff.mp contextualEmpty
    have innerSplit := append_eq_empty_iff.mp outerSplit.right
    exact And.intro outerSplit.left
      (And.intro (EigenSingletonCarrier_empty_iff.mpr innerSplit.left) innerSplit.right)
  · intro data
    have hEmpty : hsame h BHist.Empty :=
      EigenSingletonCarrier_empty_iff.mp data.right.left
    have innerEmpty : hsame (append h R) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro hEmpty data.right.right)
    have contextualEmpty : hsame (append L (append h R)) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro data.left innerEmpty)
    exact EigenSingletonCarrier_empty_iff.mpr contextualEmpty

def EigenSingletonClassifier (h k : BHist) : Prop :=
  EigenSingletonCarrier h ∧ EigenSingletonCarrier k ∧ hsame h k

theorem EigenSingletonClassifier_append_context_empty_iff {L R h k : BHist} :
    EigenSingletonClassifier (append L h) (append k R) ↔
      hsame L BHist.Empty ∧ EigenSingletonClassifier h k ∧ hsame R BHist.Empty := by
  constructor
  · intro classified
    have leftEmpty : hsame (append L h) BHist.Empty :=
      EigenSingletonCarrier_empty_iff.mp classified.left
    have rightEmpty : hsame (append k R) BHist.Empty :=
      EigenSingletonCarrier_empty_iff.mp classified.right.left
    have leftSplit := append_eq_empty_iff.mp leftEmpty
    have rightSplit := append_eq_empty_iff.mp rightEmpty
    have coreClassified : EigenSingletonClassifier h k :=
      And.intro (EigenSingletonCarrier_empty_iff.mpr leftSplit.right)
        (And.intro (EigenSingletonCarrier_empty_iff.mpr rightSplit.left)
          (hsame_trans leftSplit.right (hsame_symm rightSplit.left)))
    exact And.intro leftSplit.left (And.intro coreClassified rightSplit.right)
  · intro data
    have hEmpty : hsame h BHist.Empty :=
      EigenSingletonCarrier_empty_iff.mp data.right.left.left
    have kEmpty : hsame k BHist.Empty :=
      EigenSingletonCarrier_empty_iff.mp data.right.left.right.left
    have leftEmpty : hsame (append L h) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro data.left hEmpty)
    have rightEmpty : hsame (append k R) BHist.Empty :=
      append_eq_empty_iff.mpr (And.intro kEmpty data.right.right)
    exact And.intro (EigenSingletonCarrier_empty_iff.mpr leftEmpty)
      (And.intro (EigenSingletonCarrier_empty_iff.mpr rightEmpty)
        (hsame_trans leftEmpty (hsame_symm rightEmpty)))

theorem eigen_singleton_semantic_name_certificate :
    SemanticNameCert EigenSingletonCarrier EigenSingletonCarrier EigenSingletonCarrier
      EigenSingletonClassifier := by
  have emptyCarrier : EigenSingletonCarrier BHist.Empty := by
    exact EigenSingletonCarrier_cont_result_transport
      (map := BHist.Empty) (scalar := BHist.Empty) (vector := BHist.Empty)
      (pair := BHist.Empty) (pair' := BHist.Empty)
      (hsame_refl BHist.Empty) (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
      (cont_intro rfl) (hsame_refl BHist.Empty)
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
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
        intro h k classified _carrier
        exact classified.right.left
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }

end BEDC.Derived.EigenUp
