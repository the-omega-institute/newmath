import BEDC.FKernel.Mark
import BEDC.FKernel.Hist
import BEDC.FKernel.Bundle

/-! Asking events emit internal marks together with evidence tokens. -/
namespace BEDC.FKernel.Ask

open BEDC.FKernel.Mark
open BEDC.FKernel.Hist
open BEDC.FKernel.Bundle

class AskSetup where
  ProbeName : Type
  Evidence : Type
  Ask : ProbeName → BHist → BMark → Evidence → Prop

variable [S : AskSetup]

abbrev ProbeName : Type := S.ProbeName
abbrev Evidence : Type := S.Evidence
abbrev Ask : ProbeName → BHist → BMark → Evidence → Prop := S.Ask

structure AskEvent (pi : ProbeName) (h : BHist) : Type where
  mark : BMark
  evidence : Evidence
  event : Ask pi h mark evidence

omit S in
theorem askEvent_components [AskSetup] {pi : ProbeName} {h : BHist} (ev : AskEvent pi h) :
    Ask pi h ev.mark ev.evidence := by
  exact ev.event

omit S in
theorem askEvent_witness [AskSetup] {pi : ProbeName} {h : BHist} :
    AskEvent pi h -> ∃ m : BMark, ∃ delta : Evidence, Ask pi h m delta := by
  intro ev
  cases ev with
  | mk mark evidence event =>
      exact Exists.intro mark (Exists.intro evidence event)

omit S in
theorem AskEvent_iff_exists [AskSetup] {pi : ProbeName} {h : BHist} :
    Nonempty (AskEvent pi h) ↔ ∃ m : BMark, ∃ delta : Evidence, Ask pi h m delta := by
  constructor
  · intro witness
    cases witness with
    | intro ev =>
        exact askEvent_witness ev
  · intro witness
    cases witness with
    | intro mark rest =>
        cases rest with
        | intro evidence event =>
            exact Nonempty.intro (AskEvent.mk mark evidence event)

omit S in
theorem askEvent_from_witness [AskSetup] {pi : ProbeName} {h : BHist} {m : BMark}
    {delta : Evidence} :
    Ask pi h m delta -> Nonempty (AskEvent pi h) := by
  intro event
  exact Nonempty.intro (AskEvent.mk m delta event)

omit S in
theorem askEvent_evidence_witness [AskSetup] {pi : ProbeName} {h : BHist} :
    AskEvent pi h -> Nonempty Evidence := by
  intro ev
  cases ev with
  | mk _ evidence _ =>
      exact Nonempty.intro evidence

structure AskPolicy (D : BHist → Prop) : Prop where
  total :
    ∀ {π : ProbeName} {h : BHist}, D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ
  deterministic :
    ∀ {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence},
      Ask π h m δ → Ask π h n θ → msame m n
  respectsHistory :
    ∀ {π : ProbeName} {h k : BHist} {m n : BMark} {δ θ : Evidence},
      hsame h k → Ask π h m δ → Ask π k n θ → msame m n

structure BundleAskPolicy (bundle : ProbeBundle ProbeName) (D : BHist → Prop) : Prop where
  total :
    ∀ {pi : ProbeName} {h : BHist}, InBundle pi bundle → D h →
      ∃ m : BMark, ∃ delta : Evidence, Ask pi h m delta
  deterministic :
    ∀ {pi : ProbeName} {h : BHist} {m n : BMark} {delta theta : Evidence},
      InBundle pi bundle → Ask pi h m delta → Ask pi h n theta → msame m n
  respectsHistory :
    ∀ {pi : ProbeName} {h k : BHist} {m n : BMark} {delta theta : Evidence},
      InBundle pi bundle → hsame h k → Ask pi h m delta → Ask pi k n theta → msame m n

omit S in
theorem bundleAskPolicy_of_membership_inclusion [AskSetup]
    {source target : ProbeBundle ProbeName} {D : BHist → Prop} :
    BundleAskPolicy source D →
      (∀ {pi : ProbeName}, InBundle pi target → InBundle pi source) →
      BundleAskPolicy target D := by
  intro policy subset
  constructor
  · intro pi h inTarget hD
    exact policy.total (subset inTarget) hD
  · intro pi h m n delta theta inTarget left right
    exact policy.deterministic (subset inTarget) left right
  · intro pi h k m n delta theta inTarget same left right
    exact policy.respectsHistory (subset inTarget) same left right

omit S in
theorem empty_bundleAskPolicy [AskSetup] {D : BHist → Prop} :
    BundleAskPolicy (ProbeBundle.Bnil : ProbeBundle ProbeName) D := by
  constructor
  · intro pi h inNil hD
    exact False.elim inNil
  · intro pi h m n delta theta inNil left right
    exact False.elim inNil
  · intro pi h k m n delta theta inNil same left right
    exact False.elim inNil

omit S in
theorem bundleAskPolicy_empty [AskSetup] {D : BHist → Prop} :
    BundleAskPolicy (ProbeBundle.Bnil : ProbeBundle ProbeName) D := by
  exact empty_bundleAskPolicy

omit S in
theorem bundleAskPolicy_tail [AskSetup]
    {pi : ProbeName} {tail : ProbeBundle ProbeName} {D : BHist → Prop} :
    BundleAskPolicy (ProbeBundle.Bcons pi tail) D → BundleAskPolicy tail D := by
  intro policy
  constructor
  · intro rho h inTail hD
    exact policy.total (Or.inr inTail) hD
  · intro rho h m n delta theta inTail left right
    exact policy.deterministic (Or.inr inTail) left right
  · intro rho h k m n delta theta inTail same left right
    exact policy.respectsHistory (Or.inr inTail) same left right

omit S in
theorem askPolicy_to_bundleAskPolicy [AskSetup] {bundle : ProbeBundle ProbeName}
    {D : BHist → Prop} :
    AskPolicy D → BundleAskPolicy bundle D := by
  intro policy
  induction bundle with
  | Bnil =>
      constructor
      · intro _ _ inNil _
        exact False.elim inNil
      · intro _ _ _ _ _ _ _ left right
        exact policy.deterministic left right
      · intro _ _ _ _ _ _ _ _ same left right
        exact policy.respectsHistory same left right
  | Bcons _ tail ih =>
      constructor
      · intro pi h inCons hD
        cases inCons with
        | inl _ =>
            exact policy.total hD
        | inr inTail =>
            exact ih.total inTail hD
      · intro pi h m n delta theta inCons left right
        cases inCons with
        | inl _ =>
            exact policy.deterministic left right
        | inr inTail =>
            exact ih.deterministic inTail left right
      · intro pi h k m n delta theta inCons same left right
        cases inCons with
        | inl _ =>
            exact policy.respectsHistory same left right
        | inr inTail =>
            exact ih.respectsHistory inTail same left right

omit S in
theorem bundleAskPolicy_restrict_by_inclusion [AskSetup]
    {source target : ProbeBundle ProbeName} {D : BHist → Prop} :
    BundleAskPolicy source D →
      (∀ {pi : ProbeName}, InBundle pi target → InBundle pi source) →
      BundleAskPolicy target D := by
  intro policy included
  constructor
  · intro pi h inTarget hD
    exact policy.total (included inTarget) hD
  · intro pi h m n delta theta inTarget left right
    exact policy.deterministic (included inTarget) left right
  · intro pi h k m n delta theta inTarget same left right
    exact policy.respectsHistory (included inTarget) same left right

omit S in
theorem bundleAskPolicy_append_restriction [AskSetup]
    {left right : ProbeBundle ProbeName} {D : BHist → Prop} :
    BundleAskPolicy (bundleAppend left right) D →
      BundleAskPolicy left D ∧ BundleAskPolicy right D := by
  intro policy
  constructor
  · constructor
    · intro pi h inLeft hD
      have inApp : InBundle pi (bundleAppend left right) :=
        (inBundle_bundleAppend_iff (p := pi) (left := left) (right := right)).mpr
          (Or.inl inLeft)
      exact policy.total inApp hD
    · intro pi h m n delta theta inLeft first second
      have inApp : InBundle pi (bundleAppend left right) :=
        (inBundle_bundleAppend_iff (p := pi) (left := left) (right := right)).mpr
          (Or.inl inLeft)
      exact policy.deterministic inApp first second
    · intro pi h k m n delta theta inLeft same first second
      have inApp : InBundle pi (bundleAppend left right) :=
        (inBundle_bundleAppend_iff (p := pi) (left := left) (right := right)).mpr
          (Or.inl inLeft)
      exact policy.respectsHistory inApp same first second
  · constructor
    · intro pi h inRight hD
      have inApp : InBundle pi (bundleAppend left right) :=
        (inBundle_bundleAppend_iff (p := pi) (left := left) (right := right)).mpr
          (Or.inr inRight)
      exact policy.total inApp hD
    · intro pi h m n delta theta inRight first second
      have inApp : InBundle pi (bundleAppend left right) :=
        (inBundle_bundleAppend_iff (p := pi) (left := left) (right := right)).mpr
          (Or.inr inRight)
      exact policy.deterministic inApp first second
    · intro pi h k m n delta theta inRight same first second
      have inApp : InBundle pi (bundleAppend left right) :=
        (inBundle_bundleAppend_iff (p := pi) (left := left) (right := right)).mpr
          (Or.inr inRight)
      exact policy.respectsHistory inApp same first second

omit S in
theorem bundleAskPolicy_append_gluing [AskSetup]
    {left right : ProbeBundle ProbeName} {D : BHist → Prop} :
    BundleAskPolicy left D → BundleAskPolicy right D →
      BundleAskPolicy (bundleAppend left right) D := by
  intro leftPolicy rightPolicy
  constructor
  · intro pi h inApp hD
    have membership :
        InBundle pi left ∨ InBundle pi right :=
      (inBundle_bundleAppend_iff (p := pi) (left := left) (right := right)).mp inApp
    cases membership with
    | inl inLeft =>
        exact leftPolicy.total inLeft hD
    | inr inRight =>
        exact rightPolicy.total inRight hD
  · intro pi h m n delta theta inApp first second
    have membership :
        InBundle pi left ∨ InBundle pi right :=
      (inBundle_bundleAppend_iff (p := pi) (left := left) (right := right)).mp inApp
    cases membership with
    | inl inLeft =>
        exact leftPolicy.deterministic inLeft first second
    | inr inRight =>
        exact rightPolicy.deterministic inRight first second
  · intro pi h k m n delta theta inApp same first second
    have membership :
        InBundle pi left ∨ InBundle pi right :=
      (inBundle_bundleAppend_iff (p := pi) (left := left) (right := right)).mp inApp
    cases membership with
    | inl inLeft =>
        exact leftPolicy.respectsHistory inLeft same first second
    | inr inRight =>
        exact rightPolicy.respectsHistory inRight same first second

omit S in
theorem askPolicy_total_event [AskSetup] {D : BHist → Prop} (policy : AskPolicy D)
    {pi : ProbeName} {h : BHist} :
    D h → Nonempty (AskEvent pi h) := by
  intro hD
  cases policy.total (π := pi) (h := h) hD with
  | intro mark rest =>
      cases rest with
      | intro evidence event =>
          exact Nonempty.intro (AskEvent.mk mark evidence event)

theorem ask_total_from_policy {D : BHist → Prop} (policy : AskPolicy D)
    {π : ProbeName} {h : BHist} :
    D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ := by
  intro hd
  exact policy.total hd

theorem ask_total {D : BHist → Prop} (policy : AskPolicy D)
    {π : ProbeName} {h : BHist} :
    D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ := by
  intro hD
  exact policy.total hD

theorem ask_deterministic {D : BHist → Prop} (policy : AskPolicy D)
    {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence} :
    Ask π h m δ → Ask π h n θ → msame m n := by
  intro left right
  exact policy.deterministic left right

omit S in
theorem askPolicy_total_deterministic_pair [AskSetup] {D : BHist → Prop}
    (policy : AskPolicy D) :
    (∀ {π : ProbeName} {h : BHist}, D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ) ∧
    (∀ {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence},
      Ask π h m δ → Ask π h n θ → msame m n) := by
  constructor
  · intro π h hD
    exact policy.total hD
  · intro π h m n δ θ left right
    exact policy.deterministic left right

omit S in
theorem askPolicy_total_respects_pair [AskSetup] {D : BHist → Prop} (policy : AskPolicy D) :
    (∀ {π : ProbeName} {h : BHist}, D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ) ∧
    (∀ {π : ProbeName} {h k : BHist} {m n : BMark} {δ θ : Evidence},
      hsame h k → Ask π h m δ → Ask π k n θ → msame m n) := by
  constructor
  · intro π h hD
    exact policy.total hD
  · intro π h k m n δ θ same left right
    exact policy.respectsHistory same left right

omit S in
theorem askPolicy_deterministic_respects_pair [AskSetup] {D : BHist → Prop}
    (policy : AskPolicy D) :
    (∀ {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence},
      Ask π h m δ → Ask π h n θ → msame m n) ∧
    (∀ {π : ProbeName} {h k : BHist} {m n : BMark} {δ θ : Evidence},
      hsame h k → Ask π h m δ → Ask π k n θ → msame m n) := by
  constructor
  · intro π h m n δ θ left right
    exact policy.deterministic left right
  · intro π h k m n δ θ same left right
    exact policy.respectsHistory same left right

omit S in
theorem AskPolicy_total_deterministic_pair [AskSetup] {D : BHist -> Prop}
    (policy : AskPolicy D) :
    (forall {pi : ProbeName} {h : BHist},
      D h -> exists m : BMark, exists delta : Evidence, Ask pi h m delta) /\
    (forall {pi : ProbeName} {h : BHist} {m n : BMark} {delta theta : Evidence},
      Ask pi h m delta -> Ask pi h n theta -> msame m n) := by
  constructor
  · intro pi h hD
    exact policy.total hD
  · intro pi h m n delta theta left right
    exact policy.deterministic left right

theorem asking_determinacy {D : BHist → Prop} (policy : AskPolicy D)
    {pi : ProbeName} {h : BHist} {m n : BMark} {delta theta : Evidence} :
    Ask pi h m delta → Ask pi h n theta → msame m n := by
  intro hm hn
  exact policy.deterministic hm hn

omit S in
theorem asking_determinacy_field [AskSetup] {D : BHist -> Prop} (policy : AskPolicy D) :
    (forall {pi : ProbeName} {h : BHist} {m n : BMark} {delta theta : Evidence},
      Ask pi h m delta -> Ask pi h n theta -> msame m n) := by
  intro pi h m n delta theta left right
  exact policy.deterministic left right

theorem ask_respects_history {D : BHist → Prop} (policy : AskPolicy D)
    {pi : ProbeName} {h k : BHist} {m n : BMark} {delta theta : Evidence} :
    hsame h k → Ask pi h m delta → Ask pi k n theta → msame m n := by
  intro same left right
  exact policy.respectsHistory same left right

omit S in
theorem askPolicy_respects_history_field [AskSetup] {D : BHist -> Prop} (policy : AskPolicy D) :
    (forall {pi : ProbeName} {h k : BHist} {m n : BMark} {delta theta : Evidence},
      hsame h k -> Ask pi h m delta -> Ask pi k n theta -> msame m n) := by
  intro pi h k m n delta theta same left right
  exact policy.respectsHistory same left right

omit S in
theorem ask_policy_fields [AskSetup] {D : BHist → Prop} (policy : AskPolicy D) :
    (∀ {π : ProbeName} {h : BHist}, D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ) ∧
    (∀ {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence},
      Ask π h m δ → Ask π h n θ → msame m n) ∧
    (∀ {π : ProbeName} {h k : BHist} {m n : BMark} {δ θ : Evidence},
      hsame h k → Ask π h m δ → Ask π k n θ → msame m n) := by
  constructor
  · intro π h hD
    exact policy.total hD
  · constructor
    · intro π h m n δ θ left right
      exact policy.deterministic left right
    · intro π h k m n δ θ same left right
      exact policy.respectsHistory same left right

omit S in
theorem askPolicy_event_determinacy_respects_fields [AskSetup] {D : BHist -> Prop}
    (policy : AskPolicy D) :
    (forall {pi : ProbeName} {h : BHist}, D h -> Nonempty (AskEvent pi h)) /\
    (forall {pi : ProbeName} {h : BHist} {m n : BMark} {delta theta : Evidence},
      Ask pi h m delta -> Ask pi h n theta -> msame m n) /\
    (forall {pi : ProbeName} {h k : BHist} {m n : BMark} {delta theta : Evidence},
      hsame h k -> Ask pi h m delta -> Ask pi k n theta -> msame m n) := by
  constructor
  · intro pi h hD
    exact askPolicy_total_event policy hD
  · constructor
    · intro pi h m n delta theta left right
      exact policy.deterministic left right
    · intro pi h k m n delta theta same left right
      exact policy.respectsHistory same left right

omit S in
theorem AskPolicy_iff_fields [AskSetup] {D : BHist → Prop} :
    AskPolicy D ↔
      ((∀ {π : ProbeName} {h : BHist}, D h → ∃ m : BMark, ∃ δ : Evidence, Ask π h m δ) ∧
      (∀ {π : ProbeName} {h : BHist} {m n : BMark} {δ θ : Evidence},
        Ask π h m δ → Ask π h n θ → msame m n) ∧
      (∀ {π : ProbeName} {h k : BHist} {m n : BMark} {δ θ : Evidence},
        hsame h k → Ask π h m δ → Ask π k n θ → msame m n)) := by
  constructor
  · intro policy
    exact ask_policy_fields policy
  · intro fields
    cases fields with
    | intro total rest =>
        cases rest with
        | intro deterministic respectsHistory =>
            exact AskPolicy.mk total deterministic respectsHistory

def MinimalAskSetup : AskSetup where
  ProbeName := Unit
  Evidence := Unit
  Ask := fun _ _ _ _ => True

end BEDC.FKernel.Ask
