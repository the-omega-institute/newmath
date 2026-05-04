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

theorem ModuleSingletonClassifier_empty_endpoints_iff {h k : BHist} :
    ModuleSingletonClassifier h k ↔ hsame h BHist.Empty ∧ hsame k BHist.Empty := by
  constructor
  · intro classified
    exact And.intro classified.left classified.right.left
  · intro endpoints
    exact And.intro endpoints.left
      (And.intro endpoints.right (hsame_trans endpoints.left (hsame_symm endpoints.right)))

theorem ModuleSingletonClassifier_hsame_endpoint_transport {h k h' k' : BHist} :
    ModuleSingletonClassifier h k -> hsame h h' -> hsame k k' ->
      ModuleSingletonClassifier h' k' ∧ hsame h' BHist.Empty ∧ hsame k' BHist.Empty := by
  intro classified sameH sameK
  have endpointH : hsame h' BHist.Empty :=
    hsame_trans (hsame_symm sameH) classified.left
  have endpointK : hsame k' BHist.Empty :=
    hsame_trans (hsame_symm sameK) classified.right.left
  have transported : ModuleSingletonClassifier h' k' :=
    Iff.mpr ModuleSingletonClassifier_empty_endpoints_iff
      (And.intro endpointH endpointK)
  exact And.intro transported (And.intro endpointH endpointK)

theorem ModuleSingletonSmul_empty_action_outputs_deterministic {r m n n' : BHist} :
    ModuleSingletonClassifier (ModuleSingletonSmul BHist.Empty m) n ->
      ModuleSingletonClassifier (ModuleSingletonSmul r BHist.Empty) n' ->
        ModuleSingletonClassifier n n' := by
  intro leftClassified rightClassified
  have leftEndpoints :
      hsame (ModuleSingletonSmul BHist.Empty m) BHist.Empty ∧ hsame n BHist.Empty :=
    Iff.mp ModuleSingletonClassifier_empty_endpoints_iff leftClassified
  have rightEndpoints :
      hsame (ModuleSingletonSmul r BHist.Empty) BHist.Empty ∧ hsame n' BHist.Empty :=
    Iff.mp ModuleSingletonClassifier_empty_endpoints_iff rightClassified
  exact Iff.mpr ModuleSingletonClassifier_empty_endpoints_iff
    (And.intro leftEndpoints.right rightEndpoints.right)

theorem ModuleSingletonSmul_nonfaithful_visible_scalar :
    (∀ {m : BHist}, ModuleSingletonCarrier m ->
      ModuleSingletonClassifier
        (ModuleSingletonSmul (BHist.e1 BHist.Empty) m)
        (ModuleSingletonSmul BHist.Empty m)) ∧
      (ModuleSingletonClassifier (BHist.e1 BHist.Empty) BHist.Empty -> False) := by
  constructor
  · intro m _carrierM
    exact Iff.mpr ModuleSingletonClassifier_empty_endpoints_iff
      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
  · intro classified
    exact not_hsame_e1_empty classified.left

theorem ModuleSingletonSmul_classifier_readback_iff {r m n : BHist} :
    ModuleSingletonCarrier m ->
      hsame (ModuleSingletonSmul r m) BHist.Empty /\
        (ModuleSingletonClassifier (ModuleSingletonSmul r m) n <->
          ModuleSingletonClassifier m n) := by
  intro carrierM
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · intro classified
      exact And.intro carrierM
        (And.intro classified.right.left
          (hsame_trans carrierM classified.right.right))
    · intro classified
      exact And.intro (hsame_refl BHist.Empty)
        (And.intro classified.right.left
          (hsame_trans (hsame_symm carrierM) classified.right.right))

theorem ModuleSingletonSmul_graph_empty_exact_iff {r m n : BHist} :
    hsame (ModuleSingletonSmul r m) BHist.Empty ∧
      (((ModuleSingletonCarrier r ∧ ModuleSingletonCarrier m ∧
        ModuleSingletonClassifier (ModuleSingletonSmul r m) n) ↔
          ModuleSingletonCarrier r ∧ ModuleSingletonCarrier m ∧ ModuleSingletonCarrier n)) := by
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · intro graph
      have endpoints :
          hsame (ModuleSingletonSmul r m) BHist.Empty ∧ hsame n BHist.Empty :=
        Iff.mp ModuleSingletonClassifier_empty_endpoints_iff graph.right.right
      exact And.intro graph.left (And.intro graph.right.left endpoints.right)
    · intro carriers
      have classified : ModuleSingletonClassifier (ModuleSingletonSmul r m) n :=
        Iff.mpr ModuleSingletonClassifier_empty_endpoints_iff
          (And.intro (hsame_refl BHist.Empty) carriers.right.right)
      exact And.intro carriers.left (And.intro carriers.right.left classified)

theorem ModuleSingletonSmul_graph_output_determinacy {r m n n' : BHist} :
    (ModuleSingletonCarrier r ∧ ModuleSingletonCarrier m ∧
      ModuleSingletonClassifier (ModuleSingletonSmul r m) n) ->
    (ModuleSingletonCarrier r ∧ ModuleSingletonCarrier m ∧
      ModuleSingletonClassifier (ModuleSingletonSmul r m) n') ->
      ModuleSingletonClassifier n n' ∧ hsame (ModuleSingletonSmul r m) BHist.Empty := by
  intro graph graph'
  have graphExact := ModuleSingletonSmul_graph_empty_exact_iff (r := r) (m := m) (n := n)
  have graphExact' := ModuleSingletonSmul_graph_empty_exact_iff (r := r) (m := m) (n := n')
  have carriers : ModuleSingletonCarrier r ∧ ModuleSingletonCarrier m ∧ ModuleSingletonCarrier n :=
    Iff.mp graphExact.right graph
  have carriers' : ModuleSingletonCarrier r ∧ ModuleSingletonCarrier m ∧ ModuleSingletonCarrier n' :=
    Iff.mp graphExact'.right graph'
  have outputClassified : ModuleSingletonClassifier n n' :=
    Iff.mpr ModuleSingletonClassifier_empty_endpoints_iff
      (And.intro carriers.right.right carriers'.right.right)
  exact And.intro outputClassified graphExact.left

theorem ModuleSingletonSmul_image_empty_endpoint_iff {h : BHist} :
    (Exists (fun r : BHist => Exists (fun m : BHist =>
      ModuleSingletonCarrier m /\ hsame h (ModuleSingletonSmul r m)))) <->
      hsame h BHist.Empty := by
  constructor
  · intro image
    cases image with
    | intro _r moduleImage =>
        cases moduleImage with
        | intro _m data =>
            exact data.right
  · intro carrier
    exact Exists.intro BHist.Empty
      (Exists.intro h (And.intro carrier carrier))

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

theorem ModuleSingletonSmul_image_semanticNameCert :
    SemanticNameCert ModuleSingletonCarrier (fun h : BHist => Exists (fun r : BHist =>
      Exists (fun m : BHist => ModuleSingletonCarrier m /\ hsame h (ModuleSingletonSmul r m))))
      ModuleSingletonCarrier ModuleSingletonClassifier := by
  exact {
    core := singleton_empty_history_module_laws.left.core
    pattern_sound := by
      intro h carrier
      exact Iff.mpr ModuleSingletonSmul_image_empty_endpoint_iff carrier
    ledger_sound := by
      intro _h carrier
      exact carrier
  }

theorem ModuleSingletonSmul_output_fiber_semanticNameCert {r m n : BHist} :
    ModuleSingletonCarrier r -> ModuleSingletonCarrier m ->
      ModuleSingletonClassifier (ModuleSingletonSmul r m) n ->
        SemanticNameCert
          (fun out : BHist => ModuleSingletonClassifier (ModuleSingletonSmul r m) out)
          (fun out : BHist => ModuleSingletonClassifier (ModuleSingletonSmul r m) out)
          (fun out : BHist => ModuleSingletonClassifier (ModuleSingletonSmul r m) out)
          ModuleSingletonClassifier := by
  intro _carrierR _carrierM classified
  exact {
    core := {
      carrier_inhabited := Exists.intro n classified
      equiv_refl := by
        intro out source
        exact singleton_empty_history_module_laws.left.core.equiv_refl source.right.left
      equiv_symm := by
        intro out out' same
        exact singleton_empty_history_module_laws.left.core.equiv_symm same
      equiv_trans := by
        intro out out' out'' same same'
        exact singleton_empty_history_module_laws.left.core.equiv_trans same same'
      carrier_respects_equiv := by
        intro out out' same source
        exact singleton_empty_history_module_laws.left.core.equiv_trans source same
    }
    pattern_sound := by
      intro _out source
      exact source
    ledger_sound := by
      intro _out source
      exact source
  }

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

theorem ModuleSingleton_scalar_action_laws :
    (forall r m : BHist, ModuleSingletonCarrier (ModuleSingletonSmul r m)) ∧
      (forall {r r' m m' : BHist},
        ModuleSingletonClassifier r r' ->
        ModuleSingletonClassifier m m' ->
        ModuleSingletonClassifier (ModuleSingletonSmul r m) (ModuleSingletonSmul r' m')) ∧
      (forall r s m : BHist,
        ModuleSingletonClassifier
          (ModuleSingletonSmul (ModuleSingletonMul r s) m)
          (ModuleSingletonSmul r (ModuleSingletonSmul s m))) ∧
      (forall r m n : BHist,
        ModuleSingletonClassifier
          (ModuleSingletonSmul r (ModuleSingletonAdd m n))
          (ModuleSingletonAdd (ModuleSingletonSmul r m) (ModuleSingletonSmul r n))) ∧
      (forall r s m : BHist,
        ModuleSingletonClassifier
          (ModuleSingletonSmul (ModuleSingletonAdd r s) m)
          (ModuleSingletonAdd (ModuleSingletonSmul r m) (ModuleSingletonSmul s m))) ∧
      (forall {m : BHist}, ModuleSingletonCarrier m ->
        ModuleSingletonClassifier (ModuleSingletonSmul ModuleSingletonOne m) m) := by
  constructor
  · intro r m
    exact hsame_refl BHist.Empty
  · constructor
    · intro r r' m m' sameR sameM
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

theorem ModuleSingletonSmul_scalar_representative_transport_compatibility
    {r r' s s' m m' : BHist} :
    ModuleSingletonClassifier r r' ->
      ModuleSingletonClassifier s s' ->
        ModuleSingletonClassifier m m' ->
          hsame (ModuleSingletonSmul r (ModuleSingletonSmul s m)) BHist.Empty ∧
            ModuleSingletonClassifier (ModuleSingletonSmul r (ModuleSingletonSmul s m))
              (ModuleSingletonSmul (ModuleSingletonMul r' s') m') := by
  intro sameR sameS sameM
  have smulSM :
      ModuleSingletonClassifier (ModuleSingletonSmul s m) (ModuleSingletonSmul s' m') :=
    ModuleSingleton_scalar_action_laws.right.left sameS sameM
  have nestedClassified :
      ModuleSingletonClassifier
        (ModuleSingletonSmul r (ModuleSingletonSmul s m))
        (ModuleSingletonSmul r' (ModuleSingletonSmul s' m')) :=
    ModuleSingleton_scalar_action_laws.right.left sameR smulSM
  have reassocClassified :
      ModuleSingletonClassifier
        (ModuleSingletonSmul r' (ModuleSingletonSmul s' m'))
        (ModuleSingletonSmul (ModuleSingletonMul r' s') m') :=
    singleton_empty_history_module_laws.left.core.equiv_symm
      (ModuleSingleton_scalar_action_laws.right.right.left r' s' m')
  exact And.intro (hsame_refl BHist.Empty)
    (singleton_empty_history_module_laws.left.core.equiv_trans
      nestedClassified reassocClassified)

def ModuleParityEps : BHist :=
  BHist.e0 BHist.Empty

def ModuleParityOne : BHist :=
  BHist.e1 BHist.Empty

def ModuleParityMul : BHist -> BHist -> BHist
  | BHist.Empty, h => h
  | BHist.e0 BHist.Empty, BHist.Empty => BHist.e0 BHist.Empty
  | BHist.e0 BHist.Empty, BHist.e0 BHist.Empty => BHist.Empty
  | BHist.e0 BHist.Empty, BHist.e0 (BHist.e0 _h) => BHist.Empty
  | BHist.e0 BHist.Empty, BHist.e0 (BHist.e1 _h) => BHist.Empty
  | BHist.e0 BHist.Empty, BHist.e1 _h => BHist.Empty
  | BHist.e0 (BHist.e0 _h), _ => BHist.Empty
  | BHist.e0 (BHist.e1 _h), _ => BHist.Empty
  | BHist.e1 h, BHist.Empty => BHist.e1 h
  | BHist.e1 _h, BHist.e0 _k => BHist.Empty
  | BHist.e1 _h, BHist.e1 _k => BHist.Empty

def ModuleParitySmul : BHist -> BHist -> BHist
  | BHist.Empty, _ => BHist.Empty
  | BHist.e0 BHist.Empty, BHist.Empty => BHist.e1 BHist.Empty
  | BHist.e0 BHist.Empty, BHist.e0 _h => BHist.Empty
  | BHist.e0 BHist.Empty, BHist.e1 _h => BHist.Empty
  | BHist.e0 (BHist.e0 _h), h => h
  | BHist.e0 (BHist.e1 _h), h => h
  | BHist.e1 _h, h => h

theorem ModuleParityAction_scalar_associativity_counterexample :
    hsame (ModuleParitySmul (ModuleParityMul ModuleParityEps ModuleParityEps) ModuleParityOne)
      BHist.Empty /\
      hsame (ModuleParitySmul ModuleParityEps (ModuleParitySmul ModuleParityEps ModuleParityOne))
        ModuleParityOne /\
        (hsame
          (ModuleParitySmul (ModuleParityMul ModuleParityEps ModuleParityEps) ModuleParityOne)
          (ModuleParitySmul ModuleParityEps (ModuleParitySmul ModuleParityEps ModuleParityOne)) ->
            False) := by
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · exact hsame_refl ModuleParityOne
    · intro same
      exact not_hsame_emp_e1 same

end BEDC.Derived.ModuleUp
