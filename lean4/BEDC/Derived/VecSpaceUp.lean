import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.Derived.FieldUp
import BEDC.Derived.ModuleUp

namespace BEDC.Derived.VecSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Derived.FieldUp
open BEDC.Derived.ModuleUp

theorem singleton_empty_history_vecspace_laws :
    SemanticNameCert FieldSingletonCarrier FieldSingletonCarrier FieldSingletonCarrier
      FieldSingletonClassifier ∧
      SemanticNameCert ModuleSingletonCarrier ModuleSingletonCarrier ModuleSingletonCarrier
      ModuleSingletonClassifier ∧
      (forall {a : BHist}, FieldSingletonCarrier a -> FieldSingletonNonZero a -> False) ∧
      (forall {r m : BHist}, FieldSingletonCarrier r -> ModuleSingletonCarrier m ->
        ModuleSingletonClassifier (ModuleSingletonSmul r m) BHist.Empty) ∧
      (forall {r r' m m' : BHist}, FieldSingletonClassifier r r' ->
        ModuleSingletonClassifier m m' ->
          ModuleSingletonClassifier (ModuleSingletonSmul r m) (ModuleSingletonSmul r' m')) ∧
      (forall {m : BHist}, ModuleSingletonCarrier m ->
        ModuleSingletonClassifier (ModuleSingletonSmul FieldSingletonOne m) m) := by
  have fieldLaws := BEDC.Derived.FieldUp.singleton_empty_history_field_schema_laws
  have moduleLaws := BEDC.Derived.ModuleUp.singleton_empty_history_module_laws
  have emptyModuleCarrier : ModuleSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyModuleClassified : ModuleSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyModuleCarrier
      (And.intro emptyModuleCarrier (hsame_refl BHist.Empty))
  constructor
  · exact fieldLaws.left
  · constructor
    · exact moduleLaws.left
    · constructor
      · exact fieldLaws.right.left
      · constructor
        · intro r m _carrierR _carrierM
          exact emptyModuleClassified
        · constructor
          · intro r r' m m' _sameR _sameM
            exact emptyModuleClassified
          · intro m carrierM
            exact And.intro emptyModuleCarrier
              (And.intro carrierM (hsame_symm carrierM))

theorem VecSpaceSingletonEmptyHistory_laws :
    let Carrier : BHist -> Prop := fun h => hsame h BHist.Empty
    let Classifier : BHist -> BHist -> Prop := fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    let add : BHist -> BHist -> BHist := fun _ _ => BHist.Empty
    let neg : BHist -> BHist := fun _ => BHist.Empty
    let zero : BHist := BHist.Empty
    let mul : BHist -> BHist -> BHist := fun _ _ => BHist.Empty
    let one : BHist := BHist.Empty
    let smul : BHist -> BHist -> BHist := fun _ _ => BHist.Empty
    let NonZero : BHist -> Prop := fun h => hsame h BHist.Empty ∧ hsame h (BHist.e0 BHist.Empty)
    let inv : (h : BHist) -> NonZero h -> BHist := fun _ _ => BHist.Empty
    SemanticNameCert Carrier Carrier Carrier Classifier ∧
      Carrier zero ∧
      (∀ {m : BHist}, Carrier m -> Carrier (neg m)) ∧
      (∀ {r m : BHist}, Carrier r -> Carrier m -> Classifier (smul r m) zero) ∧
      (∀ {r r' m m' : BHist}, Classifier r r' -> Classifier m m' -> Classifier (smul r m) (smul r' m')) ∧
      (∀ {r s m : BHist}, Carrier r -> Carrier s -> Carrier m -> Classifier (smul (mul r s) m) (smul r (smul s m))) ∧
      (∀ {r m n : BHist}, Carrier r -> Carrier m -> Carrier n -> Classifier (smul r (add m n)) (add (smul r m) (smul r n))) ∧
      (∀ {r s m : BHist}, Carrier r -> Carrier s -> Carrier m -> Classifier (smul (add r s) m) (add (smul r m) (smul s m))) ∧
      (∀ {m : BHist}, Carrier m -> Classifier (smul one m) m) ∧
      (∀ {a : BHist}, Carrier a -> NonZero a -> False) ∧
      (∀ {a b : BHist}, Classifier a b -> NonZero a -> NonZero b) ∧
      (∀ {a : BHist} (p : NonZero a), Carrier (inv a p)) ∧
      (∀ {a b : BHist} (p : NonZero a) (q : NonZero b), Classifier a b -> Classifier (inv a p) (inv b q)) ∧
      (∀ {a : BHist} (p : NonZero a), Classifier (mul (inv a p) a) one) ∧
      (∀ {a : BHist} (p : NonZero a), Classifier (mul a (inv a p)) one) := by
  simp only
  have emptyCarrier : hsame BHist.Empty BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : hsame BHist.Empty BHist.Empty ∧
      hsame BHist.Empty BHist.Empty ∧ hsame BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier emptyCarrier)
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
        equiv_refl := by
          intro h carrier
          exact And.intro carrier (And.intro carrier (hsame_refl h))
        equiv_symm := by
          intro h k same
          exact And.intro same.right.left
            (And.intro same.left (hsame_symm same.right.right))
        equiv_trans := by
          intro h k r sameHK sameKR
          exact And.intro sameHK.left
            (And.intro sameKR.right.left
              (hsame_trans sameHK.right.right sameKR.right.right))
        carrier_respects_equiv := by
          intro h k same _carrier
          exact same.right.left
      }
      pattern_sound := by
        intro _h carrier
        exact carrier
      ledger_sound := by
        intro _h carrier
        exact carrier
    }
  · constructor
    · exact emptyCarrier
    · constructor
      · intro m _carrierM
        exact emptyCarrier
      · constructor
        · intro r m _carrierR _carrierM
          exact emptyClassified
        · constructor
          · intro r r' m m' _sameR _sameM
            exact emptyClassified
          · constructor
            · intro r s m _carrierR _carrierS _carrierM
              exact emptyClassified
            · constructor
              · intro r m n _carrierR _carrierM _carrierN
                exact emptyClassified
              · constructor
                · intro r s m _carrierR _carrierS _carrierM
                  exact emptyClassified
                · constructor
                  · intro m carrierM
                    exact And.intro emptyCarrier (And.intro carrierM (hsame_symm carrierM))
                  · constructor
                    · intro a carrierA nonzeroA
                      exact not_hsame_emp_e0
                        (hsame_trans (hsame_symm carrierA) nonzeroA.right)
                    · constructor
                      · intro a b sameAB nonzeroA
                        exact And.intro sameAB.right.left
                          (hsame_trans (hsame_symm sameAB.right.right) nonzeroA.right)
                      · constructor
                        · intro a p
                          exact emptyCarrier
                        · constructor
                          · intro a b p q _sameAB
                            exact emptyClassified
                          · constructor
                            · intro a p
                              exact emptyClassified
                            · intro a p
                              exact emptyClassified

def VecSpaceSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def VecSpaceSingletonClassifier (h k : BHist) : Prop :=
  VecSpaceSingletonCarrier h ∧ VecSpaceSingletonCarrier k ∧ hsame h k

def VecSpaceSingletonSmul (_r _m : BHist) : BHist :=
  BHist.Empty

theorem VecSpaceSingletonSmul_classifier_empty_iff {r m t : BHist} :
    VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) t ↔ hsame t BHist.Empty := by
  constructor
  · intro classified
    exact classified.right.left
  · intro targetEmpty
    exact And.intro (hsame_refl BHist.Empty)
      (And.intro targetEmpty (hsame_symm targetEmpty))

theorem VecSpaceSingletonSmul_empty_result_readback {r m n : BHist} :
    VecSpaceSingletonCarrier m ->
      VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) n ->
        hsame (VecSpaceSingletonSmul r m) BHist.Empty ∧ VecSpaceSingletonClassifier m n := by
  intro carrierM classified
  cases classified with
  | intro actionCarrier rest =>
      cases rest with
      | intro carrierN actionSameN =>
          exact And.intro actionCarrier
            (And.intro carrierM (And.intro carrierN (hsame_trans carrierM actionSameN)))

theorem VecSpaceSingleton_semanticNameCert :
    SemanticNameCert VecSpaceSingletonCarrier VecSpaceSingletonCarrier
      VecSpaceSingletonCarrier VecSpaceSingletonClassifier := by
  have emptyCarrier : VecSpaceSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyCarrier
      equiv_refl := by
        intro h carrier
        exact And.intro carrier (And.intro carrier (hsame_refl h))
      equiv_symm := by
        intro h k same
        exact And.intro same.right.left
          (And.intro same.left (hsame_symm same.right.right))
      equiv_trans := by
        intro h k r sameHK sameKR
        exact And.intro sameHK.left
          (And.intro sameKR.right.left (hsame_trans sameHK.right.right sameKR.right.right))
      carrier_respects_equiv := by
        intro h k same _carrier
        exact same.right.left
    }
    pattern_sound := by
      intro _h carrier
      exact carrier
    ledger_sound := by
      intro _h carrier
      exact carrier
  }

theorem VecSpaceSingleton_scalar_action_inverse_law {r m : BHist}
    (p : BEDC.Derived.FieldUp.FieldSingletonNonZero r) :
    VecSpaceSingletonCarrier m ->
      VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty ∧
        VecSpaceSingletonClassifier
          (VecSpaceSingletonSmul (BEDC.Derived.FieldUp.FieldSingletonInv r p)
            (VecSpaceSingletonSmul r m))
          m := by
  intro carrierM
  constructor
  · exact And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  · exact And.intro (hsame_refl BHist.Empty)
      (And.intro carrierM (hsame_symm carrierM))

theorem VecSpaceSingletonSmul_carrier_readback {r m : BHist} :
    VecSpaceSingletonCarrier m ->
      VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) m ∧
        hsame (VecSpaceSingletonSmul r m) BHist.Empty := by
  intro carrierM
  have actionCarrier : VecSpaceSingletonCarrier (VecSpaceSingletonSmul r m) :=
    hsame_refl BHist.Empty
  have actionSameM : hsame (VecSpaceSingletonSmul r m) m :=
    hsame_symm carrierM
  constructor
  · exact And.intro actionCarrier (And.intro carrierM actionSameM)
  · exact actionCarrier

theorem VecSpaceSingletonSmul_empty_readback_classifier {r m : BHist} :
    VecSpaceSingletonCarrier m ->
      VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) BHist.Empty ∧
        VecSpaceSingletonClassifier (VecSpaceSingletonSmul r m) m := by
  intro carrierM
  constructor
  · exact And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  · exact And.intro (hsame_refl BHist.Empty)
      (And.intro carrierM (hsame_symm carrierM))

end BEDC.Derived.VecSpaceUp
