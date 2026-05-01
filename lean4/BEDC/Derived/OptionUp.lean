import BEDC.FKernel.NameCert

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def OptionHistoryCarrier (source : BHist -> Prop) (h : BHist) : Prop :=
  hsame h BHist.Empty ∨ source h

def OptionSourceExcludesEmpty (source : BHist -> Prop) : Prop :=
  forall h : BHist, source h -> hsame h BHist.Empty -> False

def TaggedOptionHistoryCarrier (S : BHist → Prop) (h : BHist) : Prop :=
  hsame h BHist.Empty ∨ ∃ a : BHist, S a ∧ hsame h (BHist.e1 a)

def TaggedOptionHistoryClassifier (S : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (h k : BHist) : Prop :=
  (hsame h BHist.Empty ∧ hsame k BHist.Empty) ∨
    ∃ a : BHist, ∃ b : BHist,
      S a ∧ S b ∧ hsame h (BHist.e1 a) ∧ hsame k (BHist.e1 b) ∧ Rel a b

theorem TaggedOptionHistoryClassifier_absent_branch_equivalence {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      (hsame h BHist.Empty <-> hsame k BHist.Empty) := by
  intro classifier
  constructor
  · intro sameHEmpty
    cases classifier with
    | inl absentPair =>
        exact absentPair.right
    | inr presentPair =>
        cases presentPair with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro _ rest =>
                    cases rest with
                    | intro _ rest =>
                        cases rest with
                        | intro sameHPresent _ =>
                            exact False.elim
                              (not_hsame_emp_e1
                                (hsame_trans (hsame_symm sameHEmpty) sameHPresent))
  · intro sameKEmpty
    cases classifier with
    | inl absentPair =>
        exact absentPair.left
    | inr presentPair =>
        cases presentPair with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro _ rest =>
                    cases rest with
                    | intro _ rest =>
                        cases rest with
                        | intro _ rest =>
                            cases rest with
                            | intro sameKPresent _ =>
                                exact False.elim
                                  (not_hsame_emp_e1
                                    (hsame_trans (hsame_symm sameKEmpty) sameKPresent))

theorem TaggedOptionHistoryClassifier_right_visible_branch_inversion {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} {h k : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      (hsame k BHist.Empty -> hsame h BHist.Empty) /\
        (forall {a : BHist}, S a -> hsame k (BHist.e1 a) ->
          exists b : BHist, exists a' : BHist,
            S b /\ S a' /\ hsame a a' /\ Rel b a' /\ hsame h (BHist.e1 b)) := by
  intro classifier
  constructor
  · intro sameKEmpty
    cases classifier with
    | inl absentPair =>
        exact absentPair.left
    | inr presentPair =>
        cases presentPair with
        | intro b restB =>
            cases restB with
            | intro a' data =>
                cases data with
                | intro _ rest =>
                    cases rest with
                    | intro _ rest =>
                        cases rest with
                        | intro _ rest =>
                            cases rest with
                            | intro sameKPresent _ =>
                                exact False.elim
                                  (not_hsame_emp_e1
                                    (hsame_trans (hsame_symm sameKEmpty) sameKPresent))
  · intro a sourceA sameKPresentA
    cases classifier with
    | inl absentPair =>
        exact False.elim
          (not_hsame_emp_e1
            (hsame_trans (hsame_symm absentPair.right) sameKPresentA))
    | inr presentPair =>
        cases presentPair with
        | intro b restB =>
            cases restB with
            | intro a' data =>
                cases data with
                | intro sourceB rest =>
                    cases rest with
                    | intro sourceA' rest =>
                        cases rest with
                        | intro sameHPresent rest =>
                            cases rest with
                            | intro sameKPresentA' relBA' =>
                                have samePayload : hsame a a' :=
                                  hsame_e1_iff.mp
                                    (hsame_trans (hsame_symm sameKPresentA) sameKPresentA')
                                exact Exists.intro b
                                  (Exists.intro a'
                                    (And.intro sourceB
                                      (And.intro sourceA'
                                        (And.intro samePayload
                                          (And.intro relBA' sameHPresent)))))

theorem TaggedOptionHistoryClassifier_trans {S : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop}
    (rel_trans : forall {a b c : BHist}, Rel a b -> Rel b c -> Rel a c)
    {h k r : BHist} :
    TaggedOptionHistoryClassifier S Rel h k ->
      TaggedOptionHistoryClassifier S Rel k r ->
        TaggedOptionHistoryClassifier S Rel h r := by
  intro classifierHK classifierKR
  cases classifierHK with
  | inl absentHK =>
      cases classifierKR with
      | inl absentKR =>
          exact Or.inl (And.intro absentHK.left absentKR.right)
      | inr presentKR =>
          cases presentKR with
          | intro c restC =>
              cases restC with
              | intro d data =>
                  cases data with
                  | intro _ rest =>
                      cases rest with
                      | intro _ rest =>
                          cases rest with
                          | intro sameKPresent _ =>
                              exact False.elim
                                (not_hsame_emp_e1
                                  (hsame_trans (hsame_symm absentHK.right) sameKPresent))
  | inr presentHK =>
      cases presentHK with
      | intro a restA =>
          cases restA with
          | intro b dataHK =>
              cases dataHK with
              | intro sourceA restHK =>
                  cases restHK with
                  | intro _ restHK =>
                      cases restHK with
                      | intro sameHPresent restHK =>
                          cases restHK with
                          | intro sameKLeft relAB =>
                              cases classifierKR with
                              | inl absentKR =>
                                  exact False.elim
                                    (not_hsame_e1_empty
                                      (hsame_trans (hsame_symm sameKLeft) absentKR.left))
                              | inr presentKR =>
                                  cases presentKR with
                                  | intro c restC =>
                                      cases restC with
                                      | intro d dataKR =>
                                          cases dataKR with
                                          | intro _ restKR =>
                                              cases restKR with
                                              | intro sourceD restKR =>
                                                  cases restKR with
                                                  | intro sameKRight restKR =>
                                                      cases restKR with
                                                      | intro sameRPresent relCD =>
                                                          have sameBC : hsame b c :=
                                                            hsame_e1_iff.mp
                                                              (hsame_trans
                                                                (hsame_symm sameKLeft)
                                                                sameKRight)
                                                          cases sameBC
                                                          exact Or.inr
                                                            (Exists.intro a
                                                              (Exists.intro d
                                                                (And.intro sourceA
                                                                  (And.intro sourceD
                                                                    (And.intro sameHPresent
                                                                      (And.intro sameRPresent
                                                                        (rel_trans relAB
                                                                          relCD)))))))

theorem TaggedOptionHistoryCarrier_present_exactness {S : BHist → Prop} {h : BHist} :
    TaggedOptionHistoryCarrier S (BHist.e1 h) ↔ ∃ a : BHist, S a ∧ hsame h a := by
  constructor
  · intro carrier
    cases carrier with
    | inl emptyCase =>
        exact False.elim (not_hsame_e1_empty emptyCase)
    | inr presentCase =>
        cases presentCase with
        | intro a data =>
            cases data with
            | intro sourceCase sameEndpoint =>
                exact Exists.intro a
                  (And.intro sourceCase (hsame_e1_iff.mp sameEndpoint))
  · intro presentCase
    cases presentCase with
    | intro a data =>
        cases data with
        | intro sourceCase samePayload =>
            exact Or.inr
              (Exists.intro a (And.intro sourceCase (hsame_e1_congr samePayload)))

theorem TaggedOptionHistoryCarrier_exclusive_branch_partition {S : BHist → Prop}
    {h : BHist} :
    TaggedOptionHistoryCarrier S h →
      (hsame h BHist.Empty ∧ ((∃ a : BHist, S a ∧ hsame h (BHist.e1 a)) → False)) ∨
        (∃ a : BHist, S a ∧ hsame h (BHist.e1 a) ∧
          (hsame h BHist.Empty → False)) := by
  intro carrier
  cases carrier with
  | inl emptyCase =>
      exact Or.inl
        (And.intro emptyCase
          (by
            intro presentCase
            cases presentCase with
            | intro a data =>
                cases data with
                | intro _ samePresent =>
                    exact not_hsame_emp_e1 (hsame_trans (hsame_symm emptyCase) samePresent)))
  | inr presentCase =>
      cases presentCase with
      | intro a data =>
          cases data with
          | intro sourceCase samePresent =>
              exact Or.inr
                (Exists.intro a
                  (And.intro sourceCase
                    (And.intro samePresent
                      (by
                        intro emptyCase
                        exact not_hsame_e1_empty
                          (hsame_trans (hsame_symm samePresent) emptyCase)))))

theorem TaggedOptionHistoryCarrier_constructor_separation {S : BHist → Prop}
    {h a : BHist} :
    hsame h BHist.Empty → S a → hsame h (BHist.e1 a) → False := by
  intro sameEmpty _ samePresent
  exact not_hsame_emp_e1 (hsame_trans (hsame_symm sameEmpty) samePresent)

theorem TaggedOptionHistoryClassifier_present_branch_equivalence {S : BHist → Prop}
    {Rel : BHist → BHist → Prop} {h k : BHist} :
    TaggedOptionHistoryClassifier S Rel h k →
      ((∃ a : BHist, S a ∧ hsame h (BHist.e1 a)) ↔
        (∃ b : BHist, S b ∧ hsame k (BHist.e1 b))) := by
  intro classifier
  constructor
  · intro presentH
    cases classifier with
    | inl absentPair =>
        cases presentH with
        | intro a data =>
            cases data with
            | intro _ sameHPresent =>
                exact False.elim
                  (not_hsame_emp_e1 (hsame_trans (hsame_symm absentPair.left) sameHPresent))
    | inr presentPair =>
        cases presentPair with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro _ rest =>
                    cases rest with
                    | intro sourceB rest =>
                        cases rest with
                        | intro _ rest =>
                            cases rest with
                            | intro sameKPresent _ =>
                                exact Exists.intro b (And.intro sourceB sameKPresent)
  · intro presentK
    cases classifier with
    | inl absentPair =>
        cases presentK with
        | intro b data =>
            cases data with
            | intro _ sameKPresent =>
                exact False.elim
                  (not_hsame_emp_e1 (hsame_trans (hsame_symm absentPair.right) sameKPresent))
    | inr presentPair =>
        cases presentPair with
        | intro a restA =>
            cases restA with
            | intro b data =>
                cases data with
                | intro sourceA rest =>
                    cases rest with
                    | intro _ rest =>
                        cases rest with
                        | intro sameHPresent _ =>
                            exact Exists.intro a (And.intro sourceA sameHPresent)

theorem OptionHistoryCarrier_hsame_transport {source : BHist -> Prop} {h k : BHist} :
    hsame h k -> OptionHistoryCarrier source h -> OptionHistoryCarrier source k := by
  intro same carrier
  cases carrier with
  | inl emptyCase =>
      exact Or.inl (hsame_trans (hsame_symm same) emptyCase)
  | inr sourceCase =>
      cases same
      exact Or.inr sourceCase

def OptionHistoryClassifier (source : BHist -> Prop) (h k : BHist) : Prop :=
  OptionHistoryCarrier source h ∧ OptionHistoryCarrier source k ∧ hsame h k

theorem OptionHistoryClassifier_symm {source : BHist → Prop} {h k : BHist} :
    OptionHistoryClassifier source h k → OptionHistoryClassifier source k h := by
  intro classifier
  cases classifier with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          exact And.intro carrierK (And.intro carrierH (hsame_symm sameHK))

theorem OptionHistoryClassifier_hsame_transport {source : BHist -> Prop}
    {h h' k k' : BHist} :
    hsame h h' -> hsame k k' -> OptionHistoryClassifier source h k ->
      OptionHistoryClassifier source h' k' := by
  intro sameH sameK classifier
  cases classifier with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          constructor
          · exact OptionHistoryCarrier_hsame_transport sameH carrierH
          · constructor
            · exact OptionHistoryCarrier_hsame_transport sameK carrierK
            · exact hsame_trans (hsame_trans (hsame_symm sameH) sameHK) sameK

def OptionHistoryLedgerPolicy (source : BHist -> Prop) (raw visible : BHist) : Prop :=
  OptionHistoryCarrier source raw ∧ hsame raw visible

theorem OptionHistoryLedgerPolicy_visible_carrier {source : BHist -> Prop}
    (source_transport : ∀ {h k : BHist}, hsame h k -> source h -> source k)
    {raw visible : BHist} :
    OptionHistoryLedgerPolicy source raw visible -> OptionHistoryCarrier source visible := by
  intro ledger
  cases ledger with
  | intro rawCarrier same =>
      cases rawCarrier with
      | inl rawEmpty =>
          exact Or.inl (hsame_trans (hsame_symm same) rawEmpty)
      | inr rawSource =>
          exact Or.inr (source_transport same rawSource)

theorem OptionHistoryLedgerPolicy_raw_visible_classifier {source : BHist -> Prop}
    (source_transport : forall {h k : BHist}, hsame h k -> source h -> source k)
    {raw visible : BHist} :
    OptionHistoryLedgerPolicy source raw visible ->
      OptionHistoryClassifier source raw visible := by
  intro ledger
  cases ledger with
  | intro rawCarrier rawVisible =>
      constructor
      · exact rawCarrier
      · constructor
        · exact OptionHistoryLedgerPolicy_visible_carrier source_transport
            ⟨rawCarrier, rawVisible⟩
        · exact rawVisible

theorem OptionHistoryLedgerPolicy_hsame_transport {source : BHist -> Prop}
    {raw raw' visible visible' : BHist} :
    hsame raw raw' -> hsame visible visible' ->
      OptionHistoryLedgerPolicy source raw visible ->
        OptionHistoryLedgerPolicy source raw' visible' := by
  intro sameRaw sameVisible ledger
  cases ledger with
  | intro rawCarrier sameRawVisible =>
      constructor
      · exact OptionHistoryCarrier_hsame_transport sameRaw rawCarrier
      · exact hsame_trans (hsame_trans (hsame_symm sameRaw) sameRawVisible) sameVisible

theorem OptionHistoryClassifier_trans {source : BEDC.FKernel.Hist.BHist -> Prop}
    {h k r : BEDC.FKernel.Hist.BHist} :
    OptionHistoryClassifier source h k -> OptionHistoryClassifier source k r ->
      OptionHistoryClassifier source h r := by
  intro sameHK sameKR
  cases sameHK with
  | intro carrierH restHK =>
      cases restHK with
      | intro _ histHK =>
          cases sameKR with
          | intro _ restKR =>
              cases restKR with
              | intro carrierR histKR =>
                  exact And.intro carrierH (And.intro carrierR (hsame_trans histHK histKR))

theorem OptionHistoryLedgerPolicy_classifier_extension {source : BHist -> Prop}
    (source_transport : forall {h k : BHist}, hsame h k -> source h -> source k)
    {raw visible target : BHist} :
    OptionHistoryLedgerPolicy source raw visible ->
      OptionHistoryClassifier source visible target ->
        OptionHistoryClassifier source raw target := by
  intro ledger visibleTarget
  exact OptionHistoryClassifier_trans
    (OptionHistoryLedgerPolicy_raw_visible_classifier source_transport ledger)
    visibleTarget

theorem OptionHistoryClassifier_empty_left_iff {source : BHist -> Prop} {k : BHist} :
    OptionHistoryClassifier source BHist.Empty k ↔ hsame k BHist.Empty := by
  constructor
  · intro classifier
    cases classifier with
    | intro _ rest =>
        cases rest with
        | intro _ same =>
            exact hsame_symm same
  · intro same
    constructor
    · exact Or.inl (hsame_refl BHist.Empty)
    · constructor
      · exact Or.inl same
      · exact hsame_symm same

theorem OptionHistoryClassifier_absent_source_separation {source : BHist → Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {h : BHist} :
    source h →
      (OptionHistoryClassifier source h BHist.Empty → False) ∧
        (OptionHistoryClassifier source BHist.Empty h → False) := by
  intro sourceH
  constructor
  · intro classifier
    exact sourceExcludesEmpty h sourceH
      ((OptionHistoryClassifier_empty_left_iff (source := source) (k := h)).mp
        (OptionHistoryClassifier_symm classifier))
  · intro classifier
    exact sourceExcludesEmpty h sourceH
      ((OptionHistoryClassifier_empty_left_iff (source := source) (k := h)).mp classifier)

theorem OptionHistoryCarrier_exclusive_readback {source : BHist -> Prop}
    (sourceExcludesEmpty : OptionSourceExcludesEmpty source) {h : BHist} :
    OptionHistoryCarrier source h ->
      (hsame h BHist.Empty /\ (source h -> False)) \/
        (source h /\ (hsame h BHist.Empty -> False)) := by
  intro carrier
  cases carrier with
  | inl emptyCase =>
      exact Or.inl
        ⟨emptyCase, by
          intro sourceCase
          exact sourceExcludesEmpty h sourceCase emptyCase⟩
  | inr sourceCase =>
      exact Or.inr
        ⟨sourceCase, by
          intro emptyCase
          exact sourceExcludesEmpty h sourceCase emptyCase⟩

theorem option_history_semantic_name_certificate (source : BHist -> Prop) :
    SemanticNameCert (OptionHistoryCarrier source) (OptionHistoryCarrier source)
      (OptionHistoryCarrier source) (OptionHistoryClassifier source) := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (Or.inl (hsame_refl BHist.Empty))
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

def OptionCarrier (A : Type) := Option A

def OptionClassifierSpec {A : Type} (sourceSame : A → A → Prop) :
    OptionCarrier A → OptionCarrier A → Prop
  | none, none => True
  | some a, some b => sourceSame a b
  | none, some _ => False
  | some _, none => False

def OptionClassifier {α : Type} (sourceSame : α → α → Prop)
    (x y : OptionCarrier α) : Prop :=
  match x, y with
  | Option.none, Option.none => True
  | Option.some a, Option.some b => sourceSame a b
  | Option.none, Option.some _ => False
  | Option.some _, Option.none => False

theorem OptionCarrier_cases {α : Type} (x : Option α) :
    x = Option.none ∨ ∃ a : α, x = Option.some a := by
  cases x with
  | none =>
      exact Or.inl rfl
  | some a =>
      exact Or.inr ⟨a, rfl⟩

theorem optionClassifierSpec_cases {A : Type} {sameA : A → A → Prop} {x y : Option A} :
    OptionClassifierSpec sameA x y →
      (x = none ∧ y = none) ∨
        (∃ a : A, ∃ b : A, x = some a ∧ y = some b ∧ sameA a b) := by
  intro h
  cases x with
  | none =>
      cases y with
      | none =>
          exact Or.inl ⟨rfl, rfl⟩
      | some b =>
          cases h
  | some a =>
      cases y with
      | none =>
          cases h
      | some b =>
          exact Or.inr ⟨a, b, rfl, rfl, h⟩

theorem option_classifier_inversion {A : Type} {sourceSame : A → A → Prop}
    {x y : Option A} :
    OptionClassifierSpec sourceSame x y →
      (x = none ∧ y = none) ∨
        (∃ a : A, ∃ b : A, x = some a ∧ y = some b ∧ sourceSame a b) := by
  exact optionClassifierSpec_cases

theorem option_stability_certificate_fields {A : Type} {sameA : A → A → Prop}
    (reflA : ∀ a, sameA a a)
    (transA : ∀ {a b c}, sameA a b → sameA b c → sameA a c) :
    (OptionClassifierSpec sameA none none) ∧
      (∀ a : A, OptionClassifierSpec sameA (some a) (some a)) ∧
      (∀ {x y z : OptionCarrier A},
        OptionClassifierSpec sameA x y →
          OptionClassifierSpec sameA y z →
            OptionClassifierSpec sameA x z) ∧
      (∀ a : A, OptionClassifierSpec sameA none (some a) → False) ∧
      (∀ a : A, OptionClassifierSpec sameA (some a) none → False) := by
  constructor
  · exact True.intro
  · constructor
    · intro a
      exact reflA a
    · constructor
      · intro x y z hxy hyz
        cases x with
        | none =>
            cases y with
            | none =>
                cases z with
                | none =>
                    exact True.intro
                | some _ =>
                    exact hyz
            | some _ =>
                cases hxy
        | some _ =>
            cases y with
            | none =>
                cases hxy
            | some _ =>
                cases z with
                | none =>
                    exact hyz
                | some _ =>
                    exact transA hxy hyz
      · constructor
        · intro a h
          exact h
        · intro a h
          exact h

theorem OptionClassifierSpec_none_some_absurd {A : Type} {rel : A → A → Prop} {a : A} :
    OptionClassifierSpec rel (Option.none : OptionCarrier A) (Option.some a) → False := by
  intro h
  exact h

theorem OptionClassifierSpec_trans {A : Type} {Rel : A → A → Prop}
    (rel_trans : ∀ {a b c : A}, Rel a b → Rel b c → Rel a c) :
    ∀ {x y z : Option A},
      OptionClassifierSpec Rel x y →
        OptionClassifierSpec Rel y z →
          OptionClassifierSpec Rel x z := by
  intro x y z hxy hyz
  cases x <;> cases y <;> cases z <;> simp [OptionClassifierSpec] at *
  exact rel_trans hxy hyz

theorem OptionClassifierSpec_hsame_symm :
    ∀ {x y : OptionCarrier BHist}, OptionClassifierSpec hsame x y →
      OptionClassifierSpec hsame y x := by
  intro x y h
  cases x with
  | none =>
      cases y with
      | none =>
          exact h
      | some _ =>
          cases h
  | some _ =>
      cases y with
      | none =>
          cases h
      | some _ =>
          exact hsame_symm h

theorem optionClassifier_some_iff {α : Type} {sourceSame : α → α → Prop} {a b : α} :
    OptionClassifier sourceSame (Option.some a) (Option.some b) ↔ sourceSame a b := by
  constructor <;> intro h <;> exact h

end BEDC.Derived.OptionUp
