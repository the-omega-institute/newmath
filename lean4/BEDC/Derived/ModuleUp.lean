import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ModuleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def ModuleSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def ModuleSingletonClassifier (h k : BHist) : Prop :=
  ModuleSingletonCarrier h ∧ ModuleSingletonCarrier k ∧ hsame h k

def ModuleSingletonAdd (_x _y : BHist) : BHist :=
  BHist.Empty

def ModuleSingletonNeg (_x : BHist) : BHist :=
  BHist.Empty

def ModuleSingletonZero : BHist :=
  BHist.Empty

def ModuleSingletonMul (_x _y : BHist) : BHist :=
  BHist.Empty

def ModuleSingletonOne : BHist :=
  BHist.Empty

def ModuleSingletonSmul (_r _m : BHist) : BHist :=
  BHist.Empty

theorem singleton_empty_history_module_laws :
    SemanticNameCert ModuleSingletonCarrier ModuleSingletonCarrier ModuleSingletonCarrier
      ModuleSingletonClassifier ∧
      (∀ {r m : BHist}, ModuleSingletonCarrier r → ModuleSingletonCarrier m →
        ModuleSingletonClassifier (ModuleSingletonSmul r m) BHist.Empty) ∧
      (∀ {r r' m m' : BHist}, ModuleSingletonClassifier r r' →
        ModuleSingletonClassifier m m' →
          ModuleSingletonClassifier (ModuleSingletonSmul r m) (ModuleSingletonSmul r' m')) ∧
      (∀ {r s m : BHist}, ModuleSingletonCarrier r → ModuleSingletonCarrier s →
        ModuleSingletonCarrier m →
          ModuleSingletonClassifier (ModuleSingletonSmul (ModuleSingletonMul r s) m)
            (ModuleSingletonSmul r (ModuleSingletonSmul s m))) ∧
      (∀ {r m n : BHist}, ModuleSingletonCarrier r → ModuleSingletonCarrier m →
        ModuleSingletonCarrier n →
          ModuleSingletonClassifier (ModuleSingletonSmul r (ModuleSingletonAdd m n))
            (ModuleSingletonAdd (ModuleSingletonSmul r m) (ModuleSingletonSmul r n))) ∧
      (∀ {r s m : BHist}, ModuleSingletonCarrier r → ModuleSingletonCarrier s →
        ModuleSingletonCarrier m →
          ModuleSingletonClassifier (ModuleSingletonSmul (ModuleSingletonAdd r s) m)
            (ModuleSingletonAdd (ModuleSingletonSmul r m) (ModuleSingletonSmul s m))) ∧
      (∀ {m : BHist}, ModuleSingletonCarrier m →
        ModuleSingletonClassifier (ModuleSingletonSmul ModuleSingletonOne m) m) := by
  have emptyCarrier : ModuleSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : ModuleSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
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
        intro h carrier
        exact carrier
      ledger_sound := by
        intro h carrier
        exact carrier
    }
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
            · intro m carrierM
              exact And.intro emptyCarrier (And.intro carrierM (hsame_symm carrierM))

theorem singleton_empty_history_module_action_fields :
    let Carrier : BHist -> Prop := fun h => hsame h BHist.Empty
    let rho : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    let add : BHist -> BHist -> BHist := fun _ _ => BHist.Empty
    let mul : BHist -> BHist -> BHist := fun _ _ => BHist.Empty
    let smul : BHist -> BHist -> BHist := fun _ _ => BHist.Empty
    (∀ {r m : BHist}, Carrier r -> Carrier m -> Carrier (smul r m)) ∧
      (∀ {r r' m m' : BHist}, rho r r' -> rho m m' ->
        rho (smul r m) (smul r' m')) ∧
      (∀ {r s m : BHist}, Carrier r -> Carrier s -> Carrier m ->
        rho (smul (mul r s) m) (smul r (smul s m))) ∧
      (∀ {r m n : BHist}, Carrier r -> Carrier m -> Carrier n ->
        rho (smul r (add m n)) (add (smul r m) (smul r n))) ∧
      (∀ {r s m : BHist}, Carrier r -> Carrier s -> Carrier m ->
        rho (smul (add r s) m) (add (smul r m) (smul s m))) ∧
      (∀ {m : BHist}, Carrier m -> rho (smul BHist.Empty m) m) := by
  dsimp
  constructor
  · intro r m carrierR carrierM
    exact hsame_refl BHist.Empty
  · constructor
    · intro r r' m m' sameR sameM
      exact And.intro (hsame_refl BHist.Empty)
        (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
    · constructor
      · intro r s m carrierR carrierS carrierM
        exact And.intro (hsame_refl BHist.Empty)
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
      · constructor
        · intro r m n carrierR carrierM carrierN
          exact And.intro (hsame_refl BHist.Empty)
            (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
        · constructor
          · intro r s m carrierR carrierS carrierM
            exact And.intro (hsame_refl BHist.Empty)
              (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
          · intro m carrierM
            exact And.intro (hsame_refl BHist.Empty)
              (And.intro carrierM (hsame_symm carrierM))

def moduleSingletonEmptyCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def moduleSingletonEmptyClassifier (h k : BHist) : Prop :=
  moduleSingletonEmptyCarrier h ∧ moduleSingletonEmptyCarrier k ∧ hsame h k

def moduleSingletonEmptyAdd (_x _y : BHist) : BHist :=
  BHist.Empty

def moduleSingletonEmptyMul (_x _y : BHist) : BHist :=
  BHist.Empty

def moduleSingletonEmptySmul (_r _m : BHist) : BHist :=
  BHist.Empty

theorem module_singleton_empty_laws :
    (moduleSingletonEmptyCarrier BHist.Empty) ∧
      (∀ r m : BHist, moduleSingletonEmptyCarrier r -> moduleSingletonEmptyCarrier m ->
        moduleSingletonEmptyCarrier (moduleSingletonEmptySmul r m)) ∧
      (∀ {r r' m m' : BHist}, moduleSingletonEmptyClassifier r r' ->
        moduleSingletonEmptyClassifier m m' ->
          moduleSingletonEmptyClassifier (moduleSingletonEmptySmul r m)
            (moduleSingletonEmptySmul r' m')) ∧
      (∀ r s m : BHist,
        moduleSingletonEmptyClassifier
          (moduleSingletonEmptySmul (moduleSingletonEmptyMul r s) m)
          (moduleSingletonEmptySmul r (moduleSingletonEmptySmul s m))) ∧
      (∀ r m n : BHist,
        moduleSingletonEmptyClassifier (moduleSingletonEmptySmul r (moduleSingletonEmptyAdd m n))
          (moduleSingletonEmptyAdd (moduleSingletonEmptySmul r m)
            (moduleSingletonEmptySmul r n))) ∧
      (∀ r s m : BHist,
        moduleSingletonEmptyClassifier (moduleSingletonEmptySmul (moduleSingletonEmptyAdd r s) m)
          (moduleSingletonEmptyAdd (moduleSingletonEmptySmul r m)
            (moduleSingletonEmptySmul s m))) ∧
      (∀ m : BHist, moduleSingletonEmptyCarrier m ->
        moduleSingletonEmptyClassifier (moduleSingletonEmptySmul BHist.Empty m) m) := by
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · intro r m hr hm
      exact hsame_refl BHist.Empty
    · constructor
      · intro r r' m m' sameRR' sameMM'
        constructor
        · exact hsame_refl BHist.Empty
        · constructor
          · exact hsame_refl BHist.Empty
          · exact hsame_refl BHist.Empty
      · constructor
        · intro r s m
          constructor
          · exact hsame_refl BHist.Empty
          · constructor
            · exact hsame_refl BHist.Empty
            · exact hsame_refl BHist.Empty
        · constructor
          · intro r m n
            constructor
            · exact hsame_refl BHist.Empty
            · constructor
              · exact hsame_refl BHist.Empty
              · exact hsame_refl BHist.Empty
          · constructor
            · intro r s m
              constructor
              · exact hsame_refl BHist.Empty
              · constructor
                · exact hsame_refl BHist.Empty
                · exact hsame_refl BHist.Empty
            · intro m carrierM
              constructor
              · exact hsame_refl BHist.Empty
              · constructor
                · exact carrierM
                · exact hsame_symm carrierM

end BEDC.Derived.ModuleUp
