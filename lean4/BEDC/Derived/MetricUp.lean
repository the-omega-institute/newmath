import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def MetricDistanceWitness (x y dist : BHist) : Prop :=
  UnaryHistory x ∧ UnaryHistory y ∧ UnaryHistory dist ∧ Cont x y dist

theorem MetricDistanceWitness_empty_distance_iff {x y : BHist} :
    MetricDistanceWitness x y BHist.Empty ↔
      hsame x BHist.Empty ∧ hsame y BHist.Empty := by
  constructor
  · intro witness
    have endpoints := cont_empty_result_inversion witness.2.2.2
    exact And.intro endpoints.1 endpoints.2
  · intro endpoints
    cases endpoints with
    | intro xEmpty yEmpty =>
        cases xEmpty
        cases yEmpty
        exact
          And.intro unary_empty
            (And.intro unary_empty (And.intro unary_empty (cont_intro rfl)))

def MetricDistanceDepth : BHist → Nat
  | BHist.Empty => 0
  | BHist.e0 h => Nat.succ (MetricDistanceDepth h)
  | BHist.e1 h => Nat.succ (MetricDistanceDepth h)

private theorem MetricDistanceDepth_append :
    ∀ x y : BHist, MetricDistanceDepth (append x y) =
      MetricDistanceDepth x + MetricDistanceDepth y := by
  intro x y
  induction y with
  | Empty =>
      rfl
  | e0 y ih =>
      exact congrArg Nat.succ ih
  | e1 y ih =>
      exact congrArg Nat.succ ih

theorem MetricDistanceWitness_depth_add {x y d : BHist} :
    MetricDistanceWitness x y d →
      MetricDistanceDepth d = MetricDistanceDepth x + MetricDistanceDepth y := by
  intro witness
  cases witness with
  | intro _xCarrier rest =>
      cases rest with
      | intro _yCarrier rest =>
          cases rest with
          | intro _dCarrier distance =>
              cases distance
              exact MetricDistanceDepth_append x y

theorem MetricDistanceWitness_prefix_iff {p x y d : BHist} :
    MetricDistanceWitness (append p x) y (append p d) ↔
      UnaryHistory p ∧ MetricDistanceWitness x y d := by
  constructor
  · intro prefixed
    cases prefixed with
    | intro prefixedSource rest =>
        cases rest with
        | intro yCarrier rest =>
            cases rest with
            | intro prefixedDist rest =>
                have pCarrier : UnaryHistory p := unary_append_left_factor prefixedSource
                have xCarrier : UnaryHistory x := unary_append_right_factor prefixedSource
                have dCarrier : UnaryHistory d := unary_append_right_factor prefixedDist
                have baseRel : Cont x y d := cont_prefix_cancel rest
                exact
                  And.intro pCarrier
                    (And.intro xCarrier (And.intro yCarrier (And.intro dCarrier baseRel)))
  · intro base
    cases base with
    | intro pCarrier witness =>
        cases witness with
        | intro xCarrier rest =>
            cases rest with
            | intro yCarrier rest =>
                cases rest with
                | intro dCarrier baseRel =>
                    exact
                      And.intro (unary_append_closed pCarrier xCarrier)
                        (And.intro yCarrier
                          (And.intro (unary_append_closed pCarrier dCarrier)
                            (cont_intro
                              ((congrArg (append p) baseRel).trans
                                (append_assoc p x y).symm))))

theorem MetricDistanceWitness_suffix_iff {p x y d : BHist} :
    MetricDistanceWitness x (append y p) (append d p) ↔
      UnaryHistory p ∧ MetricDistanceWitness x y d := by
  constructor
  · intro suffixed
    cases suffixed with
    | intro xCarrier rest =>
        cases rest with
        | intro suffixedTarget rest =>
            cases rest with
            | intro suffixedDist rest =>
                have yCarrier : UnaryHistory y := unary_append_left_factor suffixedTarget
                have pCarrier : UnaryHistory p := unary_append_right_factor suffixedTarget
                have dCarrier : UnaryHistory d := unary_append_left_factor suffixedDist
                have baseRel : Cont x y d := by
                  apply cont_intro
                  apply append_right_cancel (k := p)
                  exact rest.trans (append_assoc x y p).symm
                exact
                  And.intro pCarrier
                    (And.intro xCarrier (And.intro yCarrier (And.intro dCarrier baseRel)))
  · intro base
    cases base with
    | intro pCarrier witness =>
        cases witness with
        | intro xCarrier rest =>
            cases rest with
            | intro yCarrier rest =>
                cases rest with
                | intro dCarrier baseRel =>
                    exact
                      And.intro xCarrier
                        (And.intro (unary_append_closed yCarrier pCarrier)
                          (And.intro (unary_append_closed dCarrier pCarrier)
                            (cont_intro
                              ((congrArg (fun result => append result p) baseRel).trans
                                (append_assoc x y p)))))

theorem MetricDistanceWitness_visible_context_iff {p q x y d : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p d) q) ↔
      UnaryHistory p ∧ UnaryHistory q ∧ MetricDistanceWitness x y d := by
  constructor
  · intro visible
    have suffixPart :=
      (MetricDistanceWitness_suffix_iff (p := q) (x := append p x) (y := y)
        (d := append p d)).mp visible
    cases suffixPart with
    | intro qCarrier prefixed =>
        have prefixPart :=
          (MetricDistanceWitness_prefix_iff (p := p) (x := x) (y := y) (d := d)).mp
            prefixed
        cases prefixPart with
        | intro pCarrier witness =>
            exact And.intro pCarrier (And.intro qCarrier witness)
  · intro base
    cases base with
    | intro pCarrier rest =>
        cases rest with
        | intro qCarrier witness =>
            have prefixed :
                MetricDistanceWitness (append p x) y (append p d) :=
              (MetricDistanceWitness_prefix_iff (p := p) (x := x) (y := y) (d := d)).mpr
                (And.intro pCarrier witness)
            exact
              (MetricDistanceWitness_suffix_iff (p := q) (x := append p x) (y := y)
                (d := append p d)).mpr
                (And.intro qCarrier prefixed)

theorem MetricDistanceWitness_empty_left_iff {y d : BHist} :
    MetricDistanceWitness BHist.Empty y d ↔ UnaryHistory y ∧ hsame d y := by
  constructor
  · intro witness
    cases witness with
    | intro _emptyCarrier rest =>
        cases rest with
        | intro yCarrier rest =>
            cases rest with
            | intro _distCarrier cont =>
                exact And.intro yCarrier (cont_left_unit_result cont)
  · intro data
    cases data with
    | intro yCarrier sameDY =>
        exact
          And.intro unary_empty
            (And.intro yCarrier
              (And.intro (unary_transport yCarrier (hsame_symm sameDY))
                (cont_left_unit_iff.mpr sameDY)))

theorem MetricDistanceWitness_empty_right_iff {x d : BHist} :
    MetricDistanceWitness x BHist.Empty d ↔ UnaryHistory x ∧ hsame d x := by
  constructor
  · intro witness
    cases witness with
    | intro xCarrier rest =>
        cases rest with
        | intro _emptyCarrier rest =>
            cases rest with
            | intro _distCarrier cont =>
                exact And.intro xCarrier (cont_right_unit_iff.mp cont)
  · intro data
    cases data with
    | intro xCarrier sameDX =>
        exact
          And.intro xCarrier
            (And.intro unary_empty
              (And.intro (unary_transport xCarrier (hsame_symm sameDX))
                (cont_right_unit_iff.mpr sameDX)))

theorem MetricDistanceWitness_right_boundary_visible_context_iff
    {p q x d : BHist} :
    MetricDistanceWitness (append p x) (append BHist.Empty q) (append (append p d) q) ↔
      UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory x ∧ hsame d x := by
  constructor
  · intro visible
    have visibleData :=
      (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x)
        (y := BHist.Empty) (d := d)).mp visible
    cases visibleData with
    | intro pCarrier rest =>
        cases rest with
        | intro qCarrier central =>
            have boundary :=
              (MetricDistanceWitness_empty_right_iff (x := x) (d := d)).mp central
            exact And.intro pCarrier (And.intro qCarrier boundary)
  · intro data
    cases data with
    | intro pCarrier rest =>
        cases rest with
        | intro qCarrier boundary =>
            have central : MetricDistanceWitness x BHist.Empty d :=
              (MetricDistanceWitness_empty_right_iff (x := x) (d := d)).mpr boundary
            exact
              (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x)
                (y := BHist.Empty) (d := d)).mpr
                (And.intro pCarrier (And.intro qCarrier central))

theorem MetricDistanceWitness_symmetric_classifier {x y dxy dyx : BHist} :
    MetricDistanceWitness x y dxy -> MetricDistanceWitness y x dyx -> hsame dxy dyx := by
  intro forward reverse
  exact unary_continuation_commutativity forward.1 forward.2.1 forward.2.2.2 reverse.2.2.2

theorem MetricDistanceWitness_visible_context_symmetric_classifier {p q x y dxy dyx : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p dxy) q) ->
      MetricDistanceWitness (append p y) (append x q) (append (append p dyx) q) ->
        hsame dxy dyx := by
  intro forward reverse
  have forwardCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := dxy)).mp forward
  have reverseCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := y) (y := x)
      (d := dyx)).mp reverse
  exact MetricDistanceWitness_symmetric_classifier forwardCentral.2.2 reverseCentral.2.2

theorem MetricDistanceWitness_visible_context_result_deterministic {p q x y d d' : BHist} :
    MetricDistanceWitness (append p x) (append y q) (append (append p d) q) ->
      MetricDistanceWitness (append p x) (append y q) (append (append p d') q) ->
        hsame d d' := by
  intro left right
  have leftCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := d)).mp left
  have rightCentral :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := d')).mp right
  have leftWitness : MetricDistanceWitness x y d := leftCentral.2.2
  have rightWitness : MetricDistanceWitness x y d' := rightCentral.2.2
  exact cont_deterministic leftWitness.2.2.2 rightWitness.2.2.2

theorem MetricDistanceWitness_prefix_closed {p x y dist : BHist} :
    UnaryHistory p -> MetricDistanceWitness x y dist ->
      MetricDistanceWitness (append p x) y (append p dist) := by
  intro prefixCarrier witness
  cases witness with
  | intro xCarrier rest =>
      cases rest with
      | intro yCarrier rest =>
          cases rest with
          | intro distCarrier distRel =>
              cases distRel
              exact
                And.intro (unary_append_closed prefixCarrier xCarrier)
                  (And.intro yCarrier
                    (And.intro (unary_append_closed prefixCarrier distCarrier)
                      (cont_intro (append_assoc p x y).symm)))

theorem MetricDistanceWitness_semanticNameCert {x y : BHist} :
    UnaryHistory x -> UnaryHistory y ->
      BEDC.FKernel.NameCert.SemanticNameCert (MetricDistanceWitness x y)
        (MetricDistanceWitness x y) (MetricDistanceWitness x y) hsame := by
  intro xCarrier yCarrier
  constructor
  · constructor
    · exact
        Exists.intro (append x y)
          (And.intro xCarrier
            (And.intro yCarrier
              (And.intro (unary_append_closed xCarrier yCarrier) (cont_intro rfl))))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      cases same
      exact carrier
  · intro h source
    exact source
  · intro h source
    exact source

end BEDC.Derived.MetricUp
