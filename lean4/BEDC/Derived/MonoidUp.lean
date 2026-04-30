import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MonoidUp

open BEDC.FKernel.Hist
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

end BEDC.Derived.MonoidUp
