import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.Derived.MonoidUp
namespace BEDC.Derived.GroupUp
open BEDC.FKernel.Hist BEDC.FKernel.Cont BEDC.FKernel.NameCert
theorem concrete_singleton_history_group_laws :
    let Carrier : BHist -> Prop := fun h => hsame h BHist.Empty
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    let mul : BHist -> BHist -> BHist := BEDC.FKernel.Cont.append
    let inv : BHist -> BHist := fun _ => BHist.Empty
    let e : BHist := BHist.Empty
    Carrier e ∧
      (forall {h k : BHist}, Carrier h -> Carrier k -> Carrier (mul h k)) ∧
      (forall {h : BHist}, Carrier h -> Carrier (inv h)) ∧
      (forall {h : BHist}, Carrier h -> Classifier (mul e h) h) ∧
      (forall {h : BHist}, Carrier h -> Classifier (mul h e) h) ∧
      (forall {a b c : BHist}, Carrier a -> Carrier b -> Carrier c ->
        Classifier (mul (mul a b) c) (mul a (mul b c))) ∧
      (forall {h k h' k' : BHist}, Classifier h h' -> Classifier k k' ->
        Classifier (mul h k) (mul h' k')) ∧
      (forall {h k : BHist}, Classifier h k -> Classifier (inv h) (inv k)) ∧
      (forall {h : BHist}, Carrier h -> Classifier (mul (inv h) h) e) ∧
      (forall {h : BHist}, Carrier h -> Classifier (mul h (inv h)) e) := by
  dsimp
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · intro h k carrierH carrierK; cases carrierH; cases carrierK
      exact hsame_refl BHist.Empty
    · constructor
      · intro h _; exact hsame_refl BHist.Empty
      · constructor
        · intro h carrierH; cases carrierH; exact And.intro (hsame_refl BHist.Empty)
            (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
        · constructor
          · intro h carrierH; cases carrierH; exact And.intro (hsame_refl BHist.Empty)
              (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
          · constructor
            · intro a b c carrierA carrierB carrierC; cases carrierA; cases carrierB; cases carrierC
              exact And.intro (hsame_refl BHist.Empty) (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
            · constructor
              · intro h k h' k' sameH sameK
                cases sameH.left; cases sameH.right.left; cases sameK.left; cases sameK.right.left
                exact And.intro (hsame_refl BHist.Empty) (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
              · constructor
                · intro h k _
                  exact And.intro (hsame_refl BHist.Empty)
                    (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
                · constructor
                  · intro h carrierH; cases carrierH
                    exact And.intro (hsame_refl BHist.Empty)
                      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
                  · intro h carrierH; cases carrierH
                    exact And.intro (hsame_refl BHist.Empty)
                      (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
def GroupSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty
def GroupSingletonClassifier (h k : BHist) : Prop :=
  GroupSingletonCarrier h ∧ GroupSingletonCarrier k ∧ hsame h k
def GroupSingletonMul (x y : BHist) : BHist :=
  append x y
def GroupSingletonInv (_x : BHist) : BHist :=
  BHist.Empty
def GroupSingletonUnit : BHist :=
  BHist.Empty
theorem GroupSingletonClassifier_inverse_fiber_empty_endpoint_iff {x y : BHist} :
    GroupSingletonClassifier (GroupSingletonInv x) y ↔
      GroupSingletonCarrier y ∧ hsame (GroupSingletonInv x) BHist.Empty := by
  constructor
  · intro classified; exact And.intro classified.right.left classified.left
  · intro endpoint
    exact And.intro endpoint.right
      (And.intro endpoint.left (hsame_trans endpoint.right (hsame_symm endpoint.left)))
theorem GroupSingletonClassifier_append_context_cancel_iff {L R Q S : BHist} :
    GroupSingletonCarrier L -> GroupSingletonCarrier R ->
      (GroupSingletonClassifier (append L Q) (append R S) <-> GroupSingletonClassifier Q S) := by
  intro carrierL carrierR
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.right
      (And.intro rightSplit.right (hsame_trans leftSplit.right (hsame_symm rightSplit.right)))
  · intro classified
    have leftCarrier : GroupSingletonCarrier (append L Q) :=
      append_eq_empty_iff.mpr (And.intro carrierL classified.left)
    have rightCarrier : GroupSingletonCarrier (append R S) :=
      append_eq_empty_iff.mpr (And.intro carrierR classified.right.left)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
theorem GroupSingletonClassifier_append_unit_split_iff {p q : BHist} :
    GroupSingletonClassifier (append p q) BHist.Empty <-> GroupSingletonCarrier p ∧
      GroupSingletonCarrier q := by
  constructor
  · intro classified
    exact append_eq_empty_iff.mp classified.left
  · intro split
    exact And.intro (append_eq_empty_iff.mpr split)
      (And.intro (hsame_refl BHist.Empty) (append_eq_empty_iff.mpr split))
theorem GroupSingletonClassifier_conjugation_fixed_carrier_iff {a x : BHist} :
    GroupSingletonCarrier a ->
      (GroupSingletonClassifier (append (append a x) BHist.Empty) x <-> GroupSingletonCarrier x) := by
  intro carrierA
  constructor
  · intro classified
    exact (append_eq_empty_iff.mp (append_eq_empty_iff.mp classified.left).left).right
  · intro carrierX
    let actionCarrier : GroupSingletonCarrier (append (append a x) BHist.Empty) := append_eq_empty_iff.mpr (And.intro (append_eq_empty_iff.mpr (And.intro carrierA carrierX)) (hsame_refl BHist.Empty))
    exact And.intro actionCarrier (And.intro carrierX (hsame_trans actionCarrier (hsame_symm carrierX)))
theorem GroupSingletonClassifier_conjugation_terminal_collapse_iff {s x : BHist} :
    GroupSingletonCarrier s ->
      (GroupSingletonClassifier (append (append s x) (GroupSingletonInv s)) BHist.Empty <->
        GroupSingletonCarrier x) := by
  intro carrierS
  constructor
  · intro classified
    exact (append_eq_empty_iff.mp (GroupSingletonClassifier_append_unit_split_iff.mp classified).left).right
  · intro carrierX
    exact GroupSingletonClassifier_append_unit_split_iff.mpr (And.intro (append_eq_empty_iff.mpr (And.intro carrierS carrierX)) (hsame_refl BHist.Empty))
theorem GroupSingletonCarrier_append_visible_tail_absurd {p q : BHist} :
    (GroupSingletonCarrier (append p (BHist.e0 q)) -> False) ∧
      (GroupSingletonCarrier (append p (BHist.e1 q)) -> False) := by
  constructor
  · intro carrier
    exact not_hsame_e0_empty (append_eq_empty_iff.mp carrier).right
  · intro carrier
    exact not_hsame_e1_empty (append_eq_empty_iff.mp carrier).right
theorem GroupSingletonClassifier_normalizer_append_empty_action_certificate {s x : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x ->
      GroupSingletonCarrier (append (append s x) BHist.Empty) ∧
      GroupSingletonCarrier (append (append BHist.Empty x) BHist.Empty) ∧
      GroupSingletonClassifier (append (append s x) BHist.Empty) x ∧
      GroupSingletonClassifier
        (append (append BHist.Empty (append (append s x) BHist.Empty)) BHist.Empty) x := by
  intro carrierS carrierX
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have productCarrier : GroupSingletonCarrier (append s x) :=
    append_eq_empty_iff.mpr (And.intro carrierS carrierX)
  have actionCarrier : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro productCarrier emptyCarrier)
  have inverseActionCarrier : GroupSingletonCarrier (append (append BHist.Empty x) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro
      (append_eq_empty_iff.mpr (And.intro emptyCarrier carrierX)) emptyCarrier)
  have nestedCarrier : GroupSingletonCarrier
      (append (append BHist.Empty (append (append s x) BHist.Empty)) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro
      (append_eq_empty_iff.mpr (And.intro emptyCarrier actionCarrier)) emptyCarrier)
  exact ⟨actionCarrier, inverseActionCarrier, ⟨⟨actionCarrier, carrierX, hsame_trans actionCarrier (hsame_symm carrierX)⟩, ⟨nestedCarrier, carrierX, hsame_trans nestedCarrier (hsame_symm carrierX)⟩⟩⟩
theorem GroupSingletonHistory_laws :
    SemanticNameCert GroupSingletonCarrier GroupSingletonCarrier GroupSingletonCarrier
        GroupSingletonClassifier ∧
      (∀ {x y : BHist}, GroupSingletonCarrier x → GroupSingletonCarrier y →
        GroupSingletonCarrier (GroupSingletonMul x y)) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x → GroupSingletonCarrier (GroupSingletonInv x)) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x →
        GroupSingletonClassifier (GroupSingletonMul GroupSingletonUnit x) x) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x →
        GroupSingletonClassifier (GroupSingletonMul x GroupSingletonUnit) x) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x →
        GroupSingletonClassifier (GroupSingletonMul (GroupSingletonInv x) x)
          GroupSingletonUnit) ∧
      (∀ {x : BHist}, GroupSingletonCarrier x →
        GroupSingletonClassifier (GroupSingletonMul x (GroupSingletonInv x))
          GroupSingletonUnit) := by
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : GroupSingletonClassifier BHist.Empty BHist.Empty :=
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
    · intro x y carrierX carrierY
      cases carrierX
      cases carrierY
      exact emptyCarrier
    · constructor
      · intro x _carrierX
        exact emptyCarrier
      · constructor
        · intro x carrierX
          cases carrierX
          exact emptyClassified
        · constructor
          · intro x carrierX
            cases carrierX
            exact emptyClassified
          · constructor
            · intro x carrierX
              cases carrierX
              exact emptyClassified
            · intro x carrierX
              cases carrierX
              exact emptyClassified
theorem group_stability_certificate_fields {mul : BHist → BHist → BHist} {e : BHist}
    {inv : BHist → BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b'}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    (invCongr : ∀ {a b}, hsame a b → hsame (inv a) (inv b))
    (leftInv : ∀ x, hsame (mul (inv x) x) e)
    (rightInv : ∀ x, hsame (mul x (inv x)) e) :
    ((∀ x : BHist, BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame x x) ∧
      (∀ {x y z : BHist}, BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame x y →
        BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame y z →
          BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame x z) ∧
      (∀ x y z : BHist,
        BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame
          (mul (mul x y) z) (mul x (mul y z))) ∧
      (∀ x : BHist,
        BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame (mul e x) x) ∧
      (∀ x : BHist,
        BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame (mul x e) x) ∧
      (∀ {a a' b b' : BHist}, BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame a a' →
        BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame b b' →
          BEDC.Derived.MonoidUp.MonoidClassifierSpec hsame (mul a b) (mul a' b'))) ∧
      (∀ {a b : BHist}, hsame a b → hsame (inv a) (inv b)) ∧
      (∀ x : BHist, hsame (mul (inv x) x) e) ∧
      (∀ x : BHist, hsame (mul x (inv x)) e) := by
  constructor
  · exact BEDC.Derived.MonoidUp.monoid_stability_certificate_fields
      BEDC.FKernel.Hist.hsame_refl
      BEDC.FKernel.Hist.hsame_trans
      assocC
      leftId
      rightId
      mulCongr
  · constructor
    · intro a b same
      exact invCongr same
    · constructor
      · intro x
        exact leftInv x
      · intro x
        exact rightInv x
theorem group_inverse_identity {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (rightId : forall x : BHist, hsame (mul x e) x)
    (leftInv : forall x : BHist, hsame (mul (inv x) x) e) :
    hsame (inv e) e := by
  exact hsame_trans (hsame_symm (rightId (inv e))) (leftInv e)
theorem group_left_inverse_involutive {mul : BHist → BHist → BHist} {e : BHist}
    {inv : BHist → BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    (leftInv : ∀ x, hsame (mul (inv x) x) e) :
    ∀ x : BHist, hsame (inv (inv x)) x := by
  intro x
  exact hsame_trans (hsame_symm (rightId (inv (inv x))))
    (hsame_trans
      (mulCongr (hsame_refl (inv (inv x))) (hsame_symm (leftInv x)))
      (hsame_trans (hsame_symm (assocC (inv (inv x)) (inv x) x))
        (hsame_trans (mulCongr (leftInv (inv x)) (hsame_refl x)) (leftId x))))
theorem group_right_inverse_involutive {mul : BHist → BHist → BHist} {e : BHist}
    {inv : BHist → BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    (rightInv : ∀ x, hsame (mul x (inv x)) e) :
    ∀ x : BHist, hsame (inv (inv x)) x := by
  intro x
  exact hsame_trans (hsame_symm (leftId (inv (inv x))))
    (hsame_trans
      (mulCongr (hsame_symm (rightInv x)) (hsame_refl (inv (inv x))))
      (hsame_trans (assocC x (inv x) (inv (inv x)))
        (hsame_trans
          (mulCongr (hsame_refl x) (rightInv (inv x)))
          (rightId x))))
theorem group_left_right_inverse_uniqueness {mul : BHist → BHist → BHist} {e : BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    {x y z : BHist} :
    hsame (mul y x) e → hsame (mul x z) e → hsame y z := by
  intro left right
  exact hsame_trans (hsame_symm (rightId y))
    (hsame_trans
      (mulCongr (hsame_refl y) (hsame_symm right))
      (hsame_trans (hsame_symm (assocC y x z))
        (hsame_trans (mulCongr left (hsame_refl z)) (leftId z))))
theorem group_inverse_congruence_from_laws {mul : BHist → BHist → BHist} {e : BHist}
    {inv : BHist → BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    (leftInv : ∀ x, hsame (mul (inv x) x) e)
    (rightInv : ∀ x, hsame (mul x (inv x)) e) :
    ∀ {x y : BHist}, hsame x y → hsame (inv x) (inv y) := by
  intro x y same
  exact group_left_right_inverse_uniqueness assocC leftId rightId mulCongr
    (hsame_trans
      (hsame_symm (mulCongr (hsame_refl (inv x)) same))
      (leftInv x))
    (rightInv y)
theorem group_inverse_mul_reverse {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul e x) x)
    (rightId : forall x : BHist, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) e)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) e) :
    forall x y : BHist, hsame (inv (mul x y)) (mul (inv y) (inv x)) := by
  intro x y
  have reverseRight : hsame (mul (mul x y) (mul (inv y) (inv x))) e := by
    have inner :
        hsame (mul y (mul (inv y) (inv x))) (inv x) := by
      exact hsame_trans (hsame_symm (assocC y (inv y) (inv x)))
        (hsame_trans (mulCongr (rightInv y) (hsame_refl (inv x)))
          (leftId (inv x)))
    exact hsame_trans (assocC x y (mul (inv y) (inv x)))
      (hsame_trans (mulCongr (hsame_refl x) inner) (rightInv x))
  exact group_left_right_inverse_uniqueness assocC leftId rightId mulCongr
    (leftInv (mul x y))
    reverseRight
theorem group_inverse_cancel_from_laws {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul e x) x)
    (rightId : forall x : BHist, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) e)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) e) :
    forall {x y : BHist}, hsame (inv x) (inv y) -> hsame x y := by
  intro x y sameInv
  have sameDouble :
      hsame (inv (inv x)) (inv (inv y)) :=
    group_inverse_congruence_from_laws assocC leftId rightId mulCongr leftInv rightInv
      sameInv
  exact hsame_trans
    (hsame_symm (group_left_inverse_involutive assocC leftId rightId mulCongr leftInv x))
    (hsame_trans sameDouble
      (group_left_inverse_involutive assocC leftId rightId mulCongr leftInv y))
theorem group_mul_right_inverse_cancel {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x, hsame (mul x (inv x)) e) :
    forall a b : BHist, hsame (mul (mul a b) (inv b)) a := by
  intro a b
  exact hsame_trans (assocC a b (inv b))
    (hsame_trans (mulCongr (hsame_refl a) (rightInv b)) (rightId a))
theorem group_mul_left_inverse_cancel {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x, hsame (mul e x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x, hsame (mul (inv x) x) e) :
    forall a b : BHist, hsame (mul (inv a) (mul a b)) b := by
  intro a b
  exact hsame_trans (hsame_symm (assocC (inv a) a b))
    (hsame_trans (mulCongr (leftInv a) (hsame_refl b)) (leftId b))
theorem group_left_cancel {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x, hsame (mul e x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x, hsame (mul (inv x) x) e) {a b c : BHist} :
    hsame (mul a b) (mul a c) -> hsame b c := by
  intro sameProducts
  exact hsame_trans (hsame_symm (leftId b))
    (hsame_trans (mulCongr (hsame_symm (leftInv a)) (hsame_refl b))
      (hsame_trans (assocC (inv a) a b)
        (hsame_trans (mulCongr (hsame_refl (inv a)) sameProducts)
          (hsame_trans (hsame_symm (assocC (inv a) a c))
            (hsame_trans (mulCongr (leftInv a) (hsame_refl c)) (leftId c))))))
theorem group_left_mul_equation_solution {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x, hsame (mul e x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x, hsame (mul (inv x) x) e) {a x b : BHist} :
    hsame (mul a x) b -> hsame x (mul (inv a) b) := by
  intro sameProduct
  exact hsame_trans (hsame_symm (leftId x))
    (hsame_trans (mulCongr (hsame_symm (leftInv a)) (hsame_refl x))
      (hsame_trans (assocC (inv a) a x)
        (mulCongr (hsame_refl (inv a)) sameProduct)))
 theorem group_left_mul_equation_exact_from_empty_unit {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x b : BHist} :
    hsame (mul a x) b <-> hsame x (mul (inv a) b) := by
  constructor
  · intro sameProduct
    exact group_left_mul_equation_solution assocC leftId mulCongr leftInv sameProduct
  · intro sameSolution
    have replaceX : hsame (mul a x) (mul a (mul (inv a) b)) := by
      exact mulCongr (hsame_refl a) sameSolution
    have reassoc :
        hsame (mul a (mul (inv a) b)) (mul (mul a (inv a)) b) := by
      exact hsame_symm (assocC a (inv a) b)
    have cancelHead : hsame (mul (mul a (inv a)) b) (mul BHist.Empty b) := by
      exact mulCongr (rightInv a) (hsame_refl b)
    exact hsame_trans replaceX (hsame_trans reassoc (hsame_trans cancelHead (leftId b)))
theorem group_right_mul_equation_solution {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x, hsame (mul x (inv x)) e) {x a b : BHist} :
    hsame (mul x a) b -> hsame x (mul b (inv a)) := by
  intro sameProduct
  exact hsame_trans (hsame_symm (rightId x))
    (hsame_trans (mulCongr (hsame_refl x) (hsame_symm (rightInv a)))
      (hsame_trans (hsame_symm (assocC x a (inv a)))
        (mulCongr sameProduct (hsame_refl (inv a)))))
 theorem group_right_mul_equation_exact_from_empty_unit {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {x a b : BHist} :
    hsame (mul x a) b <-> hsame x (mul b (inv a)) := by
  constructor
  · intro sameProduct
    exact group_right_mul_equation_solution assocC rightId mulCongr rightInv sameProduct
  · intro sameSolution
    have replaceX : hsame (mul x a) (mul (mul b (inv a)) a) := by
      exact mulCongr sameSolution (hsame_refl a)
    have reassoc :
        hsame (mul (mul b (inv a)) a) (mul b (mul (inv a) a)) := by
      exact assocC b (inv a) a
    have cancelTail : hsame (mul b (mul (inv a) a)) (mul b BHist.Empty) := by
      exact mulCongr (hsame_refl b) (leftInv a)
    exact hsame_trans replaceX (hsame_trans reassoc (hsame_trans cancelTail (rightId b)))
theorem group_left_absorb_right_factor_unit {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x, hsame (mul e x) x)
    (rightId : forall x, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x, hsame (mul (inv x) x) e) {a b : BHist} :
    hsame (mul a b) a -> hsame b e := by
  intro absorb
  exact group_left_cancel assocC leftId mulCongr leftInv
    (hsame_trans absorb (hsame_symm (rightId a)))
theorem group_right_cancel {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x, hsame (mul x (inv x)) e) {a b c : BHist} :
    hsame (mul b a) (mul c a) -> hsame b c := by
  intro sameProducts
  exact hsame_trans (hsame_symm (rightId b))
    (hsame_trans (mulCongr (hsame_refl b) (hsame_symm (rightInv a)))
      (hsame_trans (hsame_symm (assocC b a (inv a)))
        (hsame_trans (mulCongr sameProducts (hsame_refl (inv a)))
          (hsame_trans (assocC c a (inv a))
            (hsame_trans (mulCongr (hsame_refl c) (rightInv a)) (rightId c))))))
theorem group_right_absorb_left_factor_unit {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x, hsame (mul e x) x)
    (rightId : forall x, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (rightInv : forall x, hsame (mul x (inv x)) e) {a b : BHist} :
    hsame (mul b a) a -> hsame b e := by
  intro absorb
  exact group_right_cancel assocC rightId mulCongr rightInv
    (hsame_trans absorb (hsame_symm (leftId a)))
theorem group_two_sided_cancel {mul : BHist -> BHist -> BHist} {e : BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x, hsame (mul e x) x)
    (rightId : forall x, hsame (mul x e) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x, hsame (mul (inv x) x) e)
    (rightInv : forall x, hsame (mul x (inv x)) e) {a b c d : BHist} :
    hsame (mul (mul a b) c) (mul (mul a d) c) -> hsame b d := by
  intro sameProducts
  have sameLeftProducts : hsame (mul a b) (mul a d) :=
    group_right_cancel assocC rightId mulCongr rightInv sameProducts
  exact group_left_cancel assocC leftId mulCongr leftInv sameLeftProducts
theorem group_left_right_inverse_unique {mul : BHist → BHist → BHist} {e : BHist}
    (assocC : ∀ x y z, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, hsame (mul e x) x)
    (rightId : ∀ x, hsame (mul x e) x)
    (mulCongr : ∀ {a a' b b' : BHist}, hsame a a' → hsame b b' →
      hsame (mul a b) (mul a' b'))
    {x y z : BHist} :
    hsame (mul y x) e → hsame (mul x z) e → hsame y z := by
  intro leftInv rightInv
  exact hsame_trans (hsame_symm (rightId y))
    (hsame_trans (mulCongr (hsame_refl y) (hsame_symm rightInv))
      (hsame_trans (hsame_symm (assocC y x z))
        (hsame_trans (mulCongr leftInv (hsame_refl z)) (leftId z))))
 theorem group_conjugation_equation_exact_from_empty_unit_iff {mul : BHist -> BHist -> BHist}
    {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a x b : BHist} :
    hsame (mul (mul a x) (inv a)) b <-> hsame x (mul (mul (inv a) b) a) := by
  constructor
  · intro sameConj
    have collapseConjRight :
        hsame (mul (mul (mul a x) (inv a)) a) (mul a x) := by
      exact hsame_trans (assocC (mul a x) (inv a) a)
        (hsame_trans (mulCongr (hsame_refl (mul a x)) (leftInv a)) (rightId (mul a x)))
    have sameLeftProduct : hsame (mul a x) (mul b a) := by
      exact hsame_trans (hsame_symm collapseConjRight)
        (mulCongr sameConj (hsame_refl a))
    exact hsame_trans (hsame_symm (leftId x))
      (hsame_trans (mulCongr (hsame_symm (leftInv a)) (hsame_refl x))
        (hsame_trans (assocC (inv a) a x)
          (hsame_trans (mulCongr (hsame_refl (inv a)) sameLeftProduct)
            (hsame_symm (assocC (inv a) b a)))))
  · intro sameMiddle
    have sameLeftProduct : hsame (mul a x) (mul b a) := by
      have replaceMiddle :
          hsame (mul a x) (mul a (mul (mul (inv a) b) a)) := by
        exact mulCongr (hsame_refl a) sameMiddle
      have reassocOuter :
          hsame (mul a (mul (mul (inv a) b) a))
            (mul (mul a (mul (inv a) b)) a) := by
        exact hsame_symm (assocC a (mul (inv a) b) a)
      have reassocInner :
          hsame (mul (mul a (mul (inv a) b)) a)
            (mul (mul (mul a (inv a)) b) a) := by
        exact mulCongr (hsame_symm (assocC a (inv a) b)) (hsame_refl a)
      have collapseHead :
          hsame (mul (mul (mul a (inv a)) b) a) (mul (mul BHist.Empty b) a) := by
        exact mulCongr (mulCongr (rightInv a) (hsame_refl b)) (hsame_refl a)
      have collapseUnit : hsame (mul (mul BHist.Empty b) a) (mul b a) := by
        exact mulCongr (leftId b) (hsame_refl a)
      exact hsame_trans replaceMiddle
        (hsame_trans reassocOuter
          (hsame_trans reassocInner (hsame_trans collapseHead collapseUnit)))
    exact hsame_trans (mulCongr sameLeftProduct (hsame_refl (inv a)))
      (hsame_trans (assocC b a (inv a))
        (hsame_trans (mulCongr (hsame_refl b) (rightInv a)) (rightId b)))
theorem GroupSingletonNormalizerOrbit_equivalence {x y z : BHist} :
    GroupSingletonCarrier x -> (let Orbit := fun p q : BHist => Exists (fun s : BHist => GroupSingletonCarrier s ∧ GroupSingletonClassifier (append (append s p) BHist.Empty) q); Orbit x x ∧ (Orbit x y -> Orbit y x) ∧ (Orbit x y -> Orbit y z -> Orbit x z)) := by
  intro carrierX; cases carrierX
  exact ⟨⟨BHist.Empty, rfl, rfl, rfl, rfl⟩,
    (fun orbitXY => by cases orbitXY with | intro s witness => cases witness.right.right.left; exact ⟨BHist.Empty, rfl, rfl, rfl, rfl⟩),
    (fun _ orbitYZ => by cases orbitYZ with | intro s witness => cases witness.right.right.left; exact ⟨BHist.Empty, rfl, rfl, rfl, rfl⟩)⟩
end BEDC.Derived.GroupUp
