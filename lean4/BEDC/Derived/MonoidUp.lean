import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.Commutativity
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.MonoidUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert

def MonoidHistoryClassifier (Carrier : BHist -> Prop) (h k : BHist) : Prop :=
  Carrier h ∧ Carrier k ∧ hsame h k

theorem monoid_history_semantic_name_certificate (Carrier : BHist -> Prop)
    (mul : BHist -> BHist -> BHist) (e : BHist) (carrier_e : Carrier e)
    (mul_closed : forall {h k : BHist}, Carrier h -> Carrier k -> Carrier (mul h k))
    (assoc : forall {a b c : BHist}, Carrier a -> Carrier b -> Carrier c ->
      hsame (mul (mul a b) c) (mul a (mul b c)))
    (left_id : forall {h : BHist}, Carrier h -> hsame (mul e h) h)
    (right_id : forall {h : BHist}, Carrier h -> hsame (mul h e) h)
    (mul_congr : forall {a a' b b' : BHist}, Carrier a -> Carrier a' -> Carrier b ->
      Carrier b' -> hsame a a' -> hsame b b' -> hsame (mul a b) (mul a' b')) :
    SemanticNameCert Carrier Carrier Carrier (MonoidHistoryClassifier Carrier) ∧
      (forall {h : BHist}, Carrier h -> MonoidHistoryClassifier Carrier (mul e h) h) ∧
      (forall {h : BHist}, Carrier h -> MonoidHistoryClassifier Carrier (mul h e) h) ∧
      (forall {a b c : BHist}, Carrier a -> Carrier b -> Carrier c ->
        MonoidHistoryClassifier Carrier (mul (mul a b) c) (mul a (mul b c))) ∧
      (forall {a a' b b' : BHist}, Carrier a -> Carrier a' -> Carrier b -> Carrier b' ->
        MonoidHistoryClassifier Carrier a a' -> MonoidHistoryClassifier Carrier b b' ->
          MonoidHistoryClassifier Carrier (mul a b) (mul a' b')) := by
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro e carrier_e
        equiv_refl := by
          intro h carrier
          exact And.intro carrier (And.intro carrier (hsame_refl h))
        equiv_symm := by
          intro h k same
          cases same with
          | intro carrierH rest =>
              cases rest with
              | intro carrierK sameHK =>
                  exact And.intro carrierK (And.intro carrierH (hsame_symm sameHK))
        equiv_trans := by
          intro h k r sameHK sameKR
          cases sameHK with
          | intro carrierH restHK =>
              cases restHK with
              | intro _ sameHistHK =>
                  cases sameKR with
                  | intro _ restKR =>
                      cases restKR with
                      | intro carrierR sameHistKR =>
                          exact And.intro carrierH
                            (And.intro carrierR (hsame_trans sameHistHK sameHistKR))
        carrier_respects_equiv := by
          intro h k same _
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
    · intro h carrierH
      exact And.intro (mul_closed carrier_e carrierH)
        (And.intro carrierH (left_id carrierH))
    · constructor
      · intro h carrierH
        exact And.intro (mul_closed carrierH carrier_e)
          (And.intro carrierH (right_id carrierH))
      · constructor
        · intro a b c carrierA carrierB carrierC
          exact And.intro (mul_closed (mul_closed carrierA carrierB) carrierC)
            (And.intro (mul_closed carrierA (mul_closed carrierB carrierC))
              (assoc carrierA carrierB carrierC))
        · intro a a' b b' carrierA carrierA' carrierB carrierB' sameA sameB
          exact And.intro (mul_closed carrierA carrierB)
            (And.intro (mul_closed carrierA' carrierB')
              (mul_congr carrierA carrierA' carrierB carrierB' sameA.right.right
                sameB.right.right))

def MonoidClassifierSpec {C : Type} (sameC : C → C → Prop) (x y : C) : Prop :=
  sameC x y

theorem monoid_stability_certificate_fields {C : Type} {sameC : C → C → Prop}
    {mul : C → C → C} {e : C} (reflC : ∀ x, sameC x x)
    (transC : ∀ {x y z}, sameC x y → sameC y z → sameC x z)
    (assocC : ∀ x y z, sameC (mul (mul x y) z) (mul x (mul y z)))
    (leftId : ∀ x, sameC (mul e x) x) (rightId : ∀ x, sameC (mul x e) x)
    (mulCongr : ∀ {a a' b b'}, sameC a a' → sameC b b' →
      sameC (mul a b) (mul a' b')) :
    (∀ x : C, MonoidClassifierSpec sameC x x) ∧
      (∀ {x y z : C}, MonoidClassifierSpec sameC x y →
        MonoidClassifierSpec sameC y z →
          MonoidClassifierSpec sameC x z) ∧
      (∀ x y z : C,
        MonoidClassifierSpec sameC (mul (mul x y) z) (mul x (mul y z))) ∧
      (∀ x : C, MonoidClassifierSpec sameC (mul e x) x) ∧
      (∀ x : C, MonoidClassifierSpec sameC (mul x e) x) ∧
      (∀ {a a' b b' : C}, MonoidClassifierSpec sameC a a' →
        MonoidClassifierSpec sameC b b' →
          MonoidClassifierSpec sameC (mul a b) (mul a' b')) := by
  constructor
  · intro x
    exact reflC x
  · constructor
    · intro x y z hxy hyz
      exact transC hxy hyz
    · constructor
      · intro x y z
        exact assocC x y z
      · constructor
        · intro x
          exact leftId x
        · constructor
          · intro x
            exact rightId x
          · intro a a' b b' haa' hbb'
            exact mulCongr haa' hbb'

theorem monoid_identity_unique {mul : BHist -> BHist -> BHist} {e e' : BHist}
    (leftId : forall x : BHist, hsame (mul e x) x)
    (rightId' : forall x : BHist, hsame (mul x e') x) :
    hsame e e' := by
  exact hsame_trans (hsame_symm (rightId' e)) (leftId e')

theorem MonoidHistoryClassifier_identity_unique (Carrier : BHist -> Prop)
    {mul : BHist -> BHist -> BHist} {e e' : BHist} (carrier_e : Carrier e)
    (carrier_e' : Carrier e')
    (leftId : forall {h : BHist}, Carrier h -> MonoidHistoryClassifier Carrier (mul e h) h)
    (rightId' : forall {h : BHist}, Carrier h ->
      MonoidHistoryClassifier Carrier (mul h e') h) :
    MonoidHistoryClassifier Carrier e e' := by
  have sameToE : hsame (mul e e') e := (rightId' carrier_e).right.right
  have sameToE' : hsame (mul e e') e' := (leftId carrier_e').right.right
  exact And.intro carrier_e (And.intro carrier_e' (hsame_trans (hsame_symm sameToE) sameToE'))

theorem history_continuation_monoid_laws :
    (∀ h : BEDC.FKernel.Hist.BHist,
      BEDC.FKernel.Cont.Cont BEDC.FKernel.Hist.BHist.Empty h h) ∧
      (∀ h : BEDC.FKernel.Hist.BHist,
        BEDC.FKernel.Cont.Cont h BEDC.FKernel.Hist.BHist.Empty h) ∧
      (∀ {a b c ab abc bc abc' : BEDC.FKernel.Hist.BHist},
        BEDC.FKernel.Cont.Cont a b ab →
          BEDC.FKernel.Cont.Cont ab c abc →
          BEDC.FKernel.Cont.Cont b c bc →
          BEDC.FKernel.Cont.Cont a bc abc' →
          BEDC.FKernel.Hist.hsame abc abc') := by
  constructor
  · exact BEDC.FKernel.Cont.cont_left_unit
  · constructor
    · exact BEDC.FKernel.Cont.cont_right_unit
    · intro a b c ab abc bc abc' hab habc hbc habc'
      cases hab
      cases habc
      cases hbc
      cases habc'
      exact BEDC.FKernel.Cont.append_assoc a b c

theorem history_continuation_nonempty_suffix_source_absurd :
    (∀ {h k : BHist}, Cont h (BHist.e0 k) h → False) ∧
      (∀ {h k : BHist}, Cont h (BHist.e1 k) h → False) := by
  constructor
  · intro h k hcont
    exact not_hsame_e0_empty (cont_right_unit_unique hcont)
  · intro h k hcont
    exact not_hsame_e1_empty (cont_right_unit_unique hcont)

theorem history_continuation_nonempty_prefix_target_absurd :
    (forall {h k : BHist}, Cont (BHist.e0 h) k k -> False) ∧
      (forall {h k : BHist}, Cont (BHist.e1 h) k k -> False) := by
  constructor
  · intro h k hcont
    exact not_hsame_e0_empty (cont_left_unit_unique hcont)
  · intro h k hcont
    exact not_hsame_e1_empty (cont_left_unit_unique hcont)

theorem unary_append_monoid_semantic_name_certificate :
    SemanticNameCert UnaryHistory UnaryHistory UnaryHistory (MonoidHistoryClassifier UnaryHistory) ∧
      (forall {h : BHist}, UnaryHistory h ->
        MonoidHistoryClassifier UnaryHistory (append BHist.Empty h) h) ∧
      (forall {h : BHist}, UnaryHistory h ->
        MonoidHistoryClassifier UnaryHistory (append h BHist.Empty) h) ∧
      (forall {a b c : BHist}, UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
        MonoidHistoryClassifier UnaryHistory (append (append a b) c) (append a (append b c))) ∧
      (forall {a a' b b' : BHist}, UnaryHistory a -> UnaryHistory a' -> UnaryHistory b ->
        UnaryHistory b' -> MonoidHistoryClassifier UnaryHistory a a' ->
          MonoidHistoryClassifier UnaryHistory b b' ->
            MonoidHistoryClassifier UnaryHistory (append a b) (append a' b')) := by
  exact monoid_history_semantic_name_certificate UnaryHistory append BHist.Empty unary_empty
    (by
      intro h k uh uk
      exact unary_append_closed uh uk)
    (by
      intro a b c _ _ _
      exact BEDC.FKernel.Cont.append_assoc a b c)
    (by
      intro h _
      exact BEDC.FKernel.Cont.append_empty_left h)
    (by
      intro h _
      exact BEDC.FKernel.Cont.append_empty_right h)
    (by
      intro a a' b b' _ _ _ _ sameA sameB
      cases sameA
      cases sameB
      exact hsame_refl (append a b))

theorem unary_append_monoid_left_identity_empty {e : BHist} :
    UnaryHistory e ->
      (forall {h : BHist}, UnaryHistory h ->
        MonoidHistoryClassifier UnaryHistory (append e h) h) ->
      MonoidHistoryClassifier UnaryHistory e BHist.Empty := by
  intro unaryE leftId
  exact MonoidHistoryClassifier_identity_unique UnaryHistory unaryE unary_empty leftId
    (by
      intro h unaryH
      exact And.intro (unary_append_closed unaryH unary_empty)
        (And.intro unaryH (BEDC.FKernel.Cont.append_empty_right h)))

theorem unary_append_monoid_right_identity_empty {e : BHist} :
    UnaryHistory e ->
      (forall {h : BHist}, UnaryHistory h ->
        MonoidHistoryClassifier UnaryHistory (append h e) h) ->
      MonoidHistoryClassifier UnaryHistory e BHist.Empty := by
  intro unaryE rightId
  have emptyToE : MonoidHistoryClassifier UnaryHistory BHist.Empty e :=
    MonoidHistoryClassifier_identity_unique UnaryHistory unary_empty unaryE
      (by
        intro h unaryH
        exact And.intro (unary_append_closed unary_empty unaryH)
          (And.intro unaryH (BEDC.FKernel.Cont.append_empty_left h)))
      rightId
  exact And.intro unaryE (And.intro unary_empty (hsame_symm emptyToE.right.right))

theorem unary_append_monoid_identity_empty_iff {e : BHist} :
    UnaryHistory e ->
      (((forall {h : BHist}, UnaryHistory h ->
        MonoidHistoryClassifier UnaryHistory (append e h) h) ∧
        (forall {h : BHist}, UnaryHistory h ->
          MonoidHistoryClassifier UnaryHistory (append h e) h)) <->
        MonoidHistoryClassifier UnaryHistory e BHist.Empty) := by
  intro unaryE
  constructor
  · intro laws
    exact unary_append_monoid_left_identity_empty unaryE laws.left
  · intro classified
    constructor
    · intro h unaryH
      cases classified.right.right
      exact And.intro (unary_append_closed unary_empty unaryH)
        (And.intro unaryH (BEDC.FKernel.Cont.append_empty_left h))
    · intro h unaryH
      cases classified.right.right
      exact And.intro (unary_append_closed unaryH unary_empty)
        (And.intro unaryH (BEDC.FKernel.Cont.append_empty_right h))

theorem unary_append_unit_product_factor_exactness {h k : BHist} :
    MonoidHistoryClassifier UnaryHistory (append h k) BHist.Empty <->
      MonoidHistoryClassifier UnaryHistory h BHist.Empty ∧
        MonoidHistoryClassifier UnaryHistory k BHist.Empty := by
  constructor
  · intro classified
    have emptyParts := append_eq_empty_iff.mp classified.right.right
    cases emptyParts.left
    cases emptyParts.right
    have emptyClassified : MonoidHistoryClassifier UnaryHistory BHist.Empty BHist.Empty :=
      And.intro unary_empty (And.intro unary_empty (hsame_refl BHist.Empty))
    exact And.intro emptyClassified emptyClassified
  · intro classified
    have appendEmpty : hsame (append h k) BHist.Empty :=
      append_eq_empty_iff.mpr
        (And.intro classified.left.right.right classified.right.right.right)
    exact And.intro (unary_append_closed classified.left.left classified.right.left)
      (And.intro unary_empty appendEmpty)

theorem MonoidHistoryClassifier_unary_append_inverse_field_singleton_collapse_iff
    (inv : BHist -> BHist)
    (invUnary : forall h : BHist, UnaryHistory h -> UnaryHistory (inv h)) :
    (((forall h : BHist, UnaryHistory h ->
        MonoidHistoryClassifier UnaryHistory (append h (inv h)) BHist.Empty) ∧
      (forall h : BHist, UnaryHistory h ->
        MonoidHistoryClassifier UnaryHistory (append (inv h) h) BHist.Empty)) <->
      (forall h : BHist, UnaryHistory h ->
        MonoidHistoryClassifier UnaryHistory h BHist.Empty)) := by
  constructor
  · intro inverseLaws h unaryH
    exact (unary_append_unit_product_factor_exactness.mp (inverseLaws.left h unaryH)).left
  · intro singletonCollapse
    constructor
    · intro h unaryH
      exact unary_append_unit_product_factor_exactness.mpr
        (And.intro (singletonCollapse h unaryH)
          (singletonCollapse (inv h) (invUnary h unaryH)))
    · intro h unaryH
      exact unary_append_unit_product_factor_exactness.mpr
        (And.intro (singletonCollapse (inv h) (invUnary h unaryH))
          (singletonCollapse h unaryH))

theorem MonoidHistoryClassifier_unary_append_singleton_collapse_obstruction :
    (forall h : BHist, UnaryHistory h ->
      MonoidHistoryClassifier UnaryHistory h BHist.Empty) -> False := by
  intro singletonCollapse
  have unaryOne : UnaryHistory (BHist.e1 BHist.Empty) :=
    unary_e1_closed unary_empty
  have classifiedOne :
      MonoidHistoryClassifier UnaryHistory (BHist.e1 BHist.Empty) BHist.Empty :=
    singletonCollapse (BHist.e1 BHist.Empty) unaryOne
  exact not_hsame_e1_empty classifiedOne.right.right

theorem unary_append_monoid_idempotent_empty_iff {e : BHist} :
    UnaryHistory e ->
      (MonoidHistoryClassifier UnaryHistory (append e e) e <->
        MonoidHistoryClassifier UnaryHistory e BHist.Empty) := by
  intro unaryE
  constructor
  · intro classified
    exact And.intro unaryE
      (And.intro unary_empty (append_right_unit_iff.mp classified.right.right))
  · intro classified
    cases classified.right.right
    exact And.intro unary_empty (And.intro unary_empty (hsame_refl BHist.Empty))

theorem unary_append_monoid_classifier_context_congr {left right a b : BHist} :
    UnaryHistory left -> UnaryHistory right -> MonoidHistoryClassifier UnaryHistory a b ->
      MonoidHistoryClassifier UnaryHistory (append left (append a right))
        (append left (append b right)) := by
  intro unaryLeft unaryRight sameAB
  cases sameAB with
  | intro unaryA rest =>
      cases rest with
      | intro _ sameHist =>
          cases sameHist
          have unaryTail : UnaryHistory (append a right) := by
            exact unary_append_closed unaryA unaryRight
          have unaryContext : UnaryHistory (append left (append a right)) := by
            exact unary_append_closed unaryLeft unaryTail
          exact And.intro unaryContext
            (And.intro unaryContext (hsame_refl (append left (append a right))))

theorem unary_append_monoid_classifier_cancel_context {left right a b : BHist} :
    UnaryHistory left -> UnaryHistory right -> UnaryHistory a -> UnaryHistory b ->
      MonoidHistoryClassifier UnaryHistory (append left (append a right))
        (append left (append b right)) ->
        MonoidHistoryClassifier UnaryHistory a b := by
  intro _ _ unaryA unaryB sameContext
  cases sameContext with
  | intro _ rest =>
      cases rest with
      | intro _ sameAppend =>
          have sameMiddle : hsame (append a right) (append b right) := by
            exact append_left_cancel (h := left) sameAppend
          have sameAB : hsame a b := by
            exact append_right_cancel (k := right) sameMiddle
          exact And.intro unaryA (And.intro unaryB sameAB)

theorem unary_append_monoid_classifier_append_context {left right a b : BHist} :
    UnaryHistory left -> UnaryHistory right ->
      MonoidHistoryClassifier UnaryHistory a b ->
        MonoidHistoryClassifier UnaryHistory (append left (append a right))
          (append left (append b right)) := by
  intro unaryLeft unaryRight classified
  cases classified with
  | intro unaryA rest =>
      cases rest with
      | intro unaryB sameAB =>
          exact And.intro
            (unary_append_closed unaryLeft (unary_append_closed unaryA unaryRight))
            (And.intro
              (unary_append_closed unaryLeft (unary_append_closed unaryB unaryRight))
              (by
                cases sameAB
                exact hsame_refl (append left (append a right))))

theorem unary_append_monoid_classifier_context_iff {left right a b : BHist} :
    UnaryHistory left -> UnaryHistory right -> UnaryHistory a -> UnaryHistory b ->
      (MonoidHistoryClassifier UnaryHistory (append left (append a right))
        (append left (append b right)) <-> MonoidHistoryClassifier UnaryHistory a b) := by
  intro unaryLeft unaryRight unaryA unaryB
  constructor
  · intro classified
    exact unary_append_monoid_classifier_cancel_context unaryLeft unaryRight unaryA unaryB
      classified
  · intro classified
    exact unary_append_monoid_classifier_append_context unaryLeft unaryRight classified

theorem unary_append_monoid_left_factor_empty_iff {h k : BHist} :
    UnaryHistory h -> UnaryHistory k ->
      (MonoidHistoryClassifier UnaryHistory (append h k) h <->
        MonoidHistoryClassifier UnaryHistory k BHist.Empty) := by
  intro unaryH unaryK
  constructor
  · intro classified
    have sameTail : hsame k BHist.Empty := by
      exact append_left_cancel (h := h) (hsame_trans classified.right.right
        (hsame_symm (BEDC.FKernel.Cont.append_empty_right h)))
    exact And.intro unaryK (And.intro unary_empty sameTail)
  · intro classified
    have sameAppend : hsame (append h k) h := by
      exact hsame_trans
        (by
          cases classified.right.right
          exact hsame_refl (append h BHist.Empty))
        (BEDC.FKernel.Cont.append_empty_right h)
    exact And.intro (unary_append_closed unaryH unaryK) (And.intro unaryH sameAppend)

theorem unary_append_monoid_commutative_classifier {a b : BHist} :
    UnaryHistory a -> UnaryHistory b ->
      MonoidHistoryClassifier UnaryHistory (append a b) (append b a) := by
  intro unaryA unaryB
  have commData := unary_append_comm_with_closed_results unaryA unaryB
  exact And.intro commData.right.left (And.intro commData.right.right commData.left)

end BEDC.Derived.MonoidUp
