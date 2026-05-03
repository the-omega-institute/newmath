import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem cont_right_cancel_hsame_result {h h' k r r' : BHist} :
    Cont h k r -> Cont h' k r' -> hsame r r' -> hsame h h' := by
  intro left right same
  apply append_right_cancel (k := k)
  exact left.symm.trans (same.trans right)

theorem cont_hsame_transport {h h' k k' r r' : BHist} :
    hsame h h' → hsame k k' → hsame r r' → Cont h k r → Cont h' k' r' := by
  intro sameH sameK sameR hcont
  cases sameH
  cases sameK
  exact BEDC.FKernel.Cont.cont_result_hsame_transport hcont sameR
theorem cont_transport_result_classified {h h' k k' r r' s : BHist} :
    hsame h h' -> hsame k k' -> hsame r r' -> Cont h k r -> Cont h' k' s ->
      Cont h' k' r' ∧ hsame r' s := by
  intro sameH sameK sameR left right
  have transported := cont_hsame_transport sameH sameK sameR left
  exact And.intro transported (cont_deterministic transported right)

theorem cont_result_hsame_iff {a f r s : BHist} :
    Cont a f r -> (Cont a f s ↔ hsame s r) := by
  intro continuation
  constructor
  · intro alternative
    exact cont_deterministic alternative continuation
  · intro sameResult
    exact cont_result_hsame_transport continuation (hsame_symm sameResult)

theorem cont_factorization_middle_hsame_iff {a b c f g bprime : BHist} :
    Cont a f b -> Cont b g c ->
      (Cont a f bprime ∧ Cont bprime g c <-> hsame bprime b) := by
  intro left right
  constructor
  · intro factorization
    exact cont_deterministic factorization.left left
  · intro sameMiddle
    have sameCanonical : hsame b bprime := hsame_symm sameMiddle
    have leftPrime : Cont a f bprime :=
      cont_result_hsame_transport left sameCanonical
    have rightPrime : Cont bprime g c :=
      cont_hsame_transport sameCanonical (hsame_refl g) (hsame_refl c) right
    exact And.intro leftPrime rightPrime

theorem cont_source_hsame_iff {a a' f r : BHist} :
    Cont a f r -> (Cont a' f r ↔ hsame a' a) := by
  intro continuation
  constructor
  · intro alternative
    exact cont_right_cancel alternative continuation
  · intro sameSource
    exact cont_hsame_transport (hsame_symm sameSource) (hsame_refl f) (hsame_refl r)
      continuation

theorem cont_cancel_common_context {a b c d ab ad left right : BHist} :
    Cont a b ab -> Cont ab c left -> Cont a d ad -> Cont ad c right ->
      hsame left right -> hsame b d := by
  intro abDef leftDef adDef rightDef same
  cases abDef
  cases adDef
  have commonSuffix : hsame (append a b) (append a d) := by
    apply append_right_cancel (k := c)
    exact leftDef.symm.trans (same.trans rightDef)
  exact append_left_cancel (h := a) commonSuffix

theorem continuation_right_cancellation {h h' k r : BHist} :
    Cont h k r -> Cont h' k r -> hsame h h' := by
  intro left right
  exact cont_right_cancel left right

theorem cont_mutual_extension_hsame {h k leftTail rightTail : BHist} :
    Cont h leftTail k -> Cont k rightTail h -> hsame h k := by
  intro left right
  have cycle : Cont h (append leftTail rightTail) h := by
    exact right.trans
      ((congrArg (fun x => append x rightTail) left).trans
        (append_assoc h leftTail rightTail))
  have tailEmpty : hsame (append leftTail rightTail) BHist.Empty :=
    cont_right_unit_unique cycle
  have leftEmpty : leftTail = BHist.Empty := (append_eq_empty_iff.mp tailEmpty).left
  cases leftEmpty
  exact left.symm

theorem cont_mutual_extension_tails_empty {h k leftTail rightTail : BHist} :
    Cont h leftTail k -> Cont k rightTail h ->
      hsame leftTail BHist.Empty ∧ hsame rightTail BHist.Empty := by
  intro left right
  have cycle : Cont h (append leftTail rightTail) h := by
    exact right.trans
      ((congrArg (fun x => append x rightTail) left).trans
        (append_assoc h leftTail rightTail))
  have tailEmpty : hsame (append leftTail rightTail) BHist.Empty :=
    cont_right_unit_unique cycle
  exact append_eq_empty_iff.mp tailEmpty

theorem cont_self_extension_tail_absurd {h tail : BHist} :
    (Cont h (BHist.e0 tail) h -> False) ∧
      (Cont h (BHist.e1 tail) h -> False) := by
  constructor
  · intro hcont
    exact not_hsame_e0_empty (cont_right_unit_unique hcont)
  · intro hcont
    exact not_hsame_e1_empty (cont_right_unit_unique hcont)

theorem cont_mutual_extension_left_tail_absurd {h k leftTail rightTail : BHist} :
    (Cont h (BHist.e0 leftTail) k -> Cont k rightTail h -> False) ∧
      (Cont h (BHist.e1 leftTail) k -> Cont k rightTail h -> False) := by
  constructor
  · intro left right
    exact not_hsame_e0_empty (cont_mutual_extension_tails_empty left right).left
  · intro left right
    exact not_hsame_e1_empty (cont_mutual_extension_tails_empty left right).left

theorem cont_mutual_extension_right_tail_absurd {h k leftTail rightTail : BHist} :
    (Cont h leftTail k -> Cont k (BHist.e0 rightTail) h -> False) ∧
      (Cont h leftTail k -> Cont k (BHist.e1 rightTail) h -> False) := by
  constructor
  · intro left right
    exact not_hsame_e0_empty (cont_mutual_extension_tails_empty left right).right
  · intro left right
    exact not_hsame_e1_empty (cont_mutual_extension_tails_empty left right).right

theorem cont_triangle_cycle_left_visible_tail_absurd {a b c k g h : BHist} :
    Cont a (BHist.e1 k) b -> Cont b g c -> Cont c h a -> False := by
  intro left right back
  have composite : Cont a (append (BHist.e1 k) g) c := by
    cases left
    exact right.trans (append_assoc a (BHist.e1 k) g)
  have cycleTails :
      hsame (append (BHist.e1 k) g) BHist.Empty ∧ hsame h BHist.Empty :=
    cont_mutual_extension_tails_empty composite back
  exact not_hsame_e1_empty (append_eq_empty_iff.mp cycleTails.left).left

theorem cont_triangle_cycle_left_zero_tail_absurd {a b c k g h : BHist} :
    Cont a (BHist.e0 k) b -> Cont b g c -> Cont c h a -> False := by
  intro left right back
  have composite : Cont a (append (BHist.e0 k) g) c := by
    cases left
    exact right.trans (append_assoc a (BHist.e0 k) g)
  have cycleTails :
      hsame (append (BHist.e0 k) g) BHist.Empty ∧ hsame h BHist.Empty :=
    cont_mutual_extension_tails_empty composite back
  exact not_hsame_e0_empty (append_eq_empty_iff.mp cycleTails.left).left

theorem cont_triangle_cycle_middle_visible_tail_absurd {a b c f k h : BHist} :
    Cont a f b -> Cont b (BHist.e1 k) c -> Cont c h a -> False := by
  intro left middle back
  have composite : Cont a (append f (BHist.e1 k)) c := by
    cases left
    exact middle.trans (append_assoc a f (BHist.e1 k))
  have cycleTails :
      hsame (append f (BHist.e1 k)) BHist.Empty ∧ hsame h BHist.Empty :=
    cont_mutual_extension_tails_empty composite back
  exact not_hsame_e1_empty (append_eq_empty_iff.mp cycleTails.left).right

theorem cont_triangle_cycle_middle_zero_tail_absurd {a b c f k h : BHist} :
    Cont a f b -> Cont b (BHist.e0 k) c -> Cont c h a -> False := by
  intro left middle back
  have composite : Cont a (append f (BHist.e0 k)) c := by
    cases left
    exact middle.trans (append_assoc a f (BHist.e0 k))
  have cycleTails :
      hsame (append f (BHist.e0 k)) BHist.Empty ∧ hsame h BHist.Empty :=
    cont_mutual_extension_tails_empty composite back
  exact not_hsame_e0_empty (append_eq_empty_iff.mp cycleTails.left).right

theorem cont_triangle_cycle_right_visible_tail_absurd {a b c f g k : BHist} :
    Cont a f b -> Cont b g c -> Cont c (BHist.e1 k) a -> False := by
  intro left middle back
  have composite : Cont a (append f g) c := by
    cases left
    exact middle.trans (append_assoc a f g)
  exact (cont_mutual_extension_right_tail_absurd.right composite back)

theorem cont_triangle_cycle_tails_empty {a b c f g h : BHist} :
    Cont a f b -> Cont b g c -> Cont c h a ->
      hsame f BHist.Empty ∧ hsame g BHist.Empty ∧ hsame h BHist.Empty ∧
        hsame a b ∧ hsame b c := by
  intro left middle back
  have composite : Cont a (append f g) c := by
    cases left
    exact middle.trans (append_assoc a f g)
  have cycleTails :
      hsame (append f g) BHist.Empty ∧ hsame h BHist.Empty :=
    cont_mutual_extension_tails_empty composite back
  have emptyParts : f = BHist.Empty ∧ g = BHist.Empty :=
    append_eq_empty_iff.mp cycleTails.left
  cases emptyParts.left
  cases emptyParts.right
  exact
    And.intro (hsame_refl BHist.Empty)
      (And.intro (hsame_refl BHist.Empty)
        (And.intro cycleTails.right
          (And.intro
            (cont_deterministic (cont_right_unit a) left)
            (cont_deterministic (cont_right_unit b) middle))))

theorem cont_cancel_hsame_left_context {a a' b d r r' : BHist} :
    Cont a b r -> Cont a' d r' -> hsame a a' -> hsame r r' -> hsame b d := by
  intro left right sameContext sameResult
  cases sameContext
  cases sameResult
  exact cont_left_cancel left right

theorem cont_composite_tail_unique {h k r f g tail : BHist} :
    Cont h f k -> Cont k g r -> Cont h tail r -> hsame tail (append f g) := by
  intro left right direct
  have composite : Cont h (append f g) r := by
    cases left
    exact right.trans (append_assoc h f g)
  exact cont_left_cancel direct composite

theorem cont_composite_tail_iff {a b c f g t : BHist} :
    Cont a f b -> Cont b g c -> (Cont f g t <-> Cont a t c) := by
  intro left right
  constructor
  · intro tail
    cases left
    cases tail
    exact right.trans (append_assoc a f g)
  · intro direct
    exact cont_composite_tail_unique left right direct

theorem cont_composite_left_factor {a b c f g fg : BHist} :
    Cont b g c -> Cont f g fg -> Cont a fg c -> Cont a f b := by
  intro right composite displayed
  have displayedWithCommonSuffix : Cont (append a f) g c := by
    cases composite
    exact cont_intro (displayed.trans (append_assoc a f g).symm)
  have sameMiddle : hsame (append a f) b :=
    cont_right_cancel displayedWithCommonSuffix right
  exact cont_result_hsame_transport (cont_intro rfl) sameMiddle

theorem cont_composite_right_factor {a b c f g fg : BHist} :
    Cont a f b -> Cont f g fg -> Cont a fg c -> Cont b g c := by
  intro left composite displayed
  cases left
  cases composite
  cases displayed
  exact cont_intro (append_assoc a f g).symm

theorem cont_composite_factorization_iff {a c f g fg : BHist} :
    Cont f g fg -> (Cont a fg c <-> ∃ b : BHist, Cont a f b ∧ Cont b g c) := by
  intro composite
  constructor
  · intro displayed
    exact ⟨append a f, cont_intro rfl,
      cont_composite_right_factor (cont_intro rfl) composite displayed⟩
  · intro factorization
    cases factorization with
    | intro b factors =>
        cases factors.left
        cases composite
        exact cont_intro (factors.right.trans (append_assoc a f g))

theorem cont_composite_canonical_middle_public_readback {a c f g fg : BHist} :
    Cont f g fg -> Cont a fg c -> Cont a f (append a f) ∧ Cont (append a f) g c ∧
      (∀ {b : BHist}, Cont a f b -> Cont b g c -> hsame (append a f) b) := by
  intro composite displayed
  exact ⟨cont_intro rfl, cont_composite_right_factor (cont_intro rfl) composite displayed,
    fun {_b} left _right => left.symm⟩

theorem cont_prefix_iff {p a b f : BHist} :
    Cont (append p a) f (append p b) ↔ Cont a f b := by
  constructor
  · intro prefixed
    exact cont_prefix_cancel prefixed
  · intro base
    exact cont_intro ((congrArg (append p) base).trans (append_assoc p a f).symm)

theorem cont_suffix_iff {a b f p : BHist} :
    Cont a (append f p) (append b p) ↔ Cont a f b := by
  constructor
  · intro suffixed
    apply cont_intro
    apply append_right_cancel (k := p)
    exact suffixed.trans (append_assoc a f p).symm
  · intro base
    apply cont_intro
    cases base
    exact append_assoc a f p

theorem cont_hsame_common_context_iff {L R P Q a b f : BHist} :
    hsame L R -> hsame P Q ->
      (Cont (append L a) (append f P) (append (append R b) Q) ↔ Cont a f b) := by
  intro sameLR samePQ
  cases sameLR
  cases samePQ
  constructor
  · intro contextual
    have withoutSuffix : Cont (append L a) f (append L b) :=
      (cont_suffix_iff (a := append L a) (b := append L b) (f := f) (p := P)).mp
        contextual
    exact (cont_prefix_iff (p := L) (a := a) (b := b) (f := f)).mp withoutSuffix
  · intro base
    have withPrefix : Cont (append L a) f (append L b) :=
      (cont_prefix_iff (p := L) (a := a) (b := b) (f := f)).mpr base
    exact (cont_suffix_iff (a := append L a) (b := append L b) (f := f) (p := P)).mpr
      withPrefix

theorem cont_parallel_factor_tails_deterministic {a b c f f' g g' : BHist} :
    Cont a f b -> Cont b g c -> Cont a f' b -> Cont b g' c ->
      hsame f f' ∧ hsame g g' := by
  intro left right left' right'
  exact And.intro (cont_left_cancel left left') (cont_left_cancel right right')

theorem append_hsame_right_context_cancel_iff {P Q a b : BHist} :
    hsame P Q -> (hsame (append a P) (append b Q) ↔ hsame a b) := by
  intro samePQ
  cases samePQ
  constructor
  · intro sameAppend
    exact append_right_cancel (k := P) sameAppend
  · intro sameAB
    cases sameAB
    rfl

theorem append_hsame_common_context_cancel_iff {L R P Q a b : BHist} :
    hsame L R -> hsame P Q ->
      (hsame (append L (append a P)) (append R (append b Q)) ↔ hsame a b) := by
  intro sameLR samePQ
  cases sameLR
  cases samePQ
  constructor
  · intro sameAppend
    have sameMiddle : hsame (append a P) (append b P) :=
      append_left_cancel (h := L) sameAppend
    exact append_right_cancel (k := P) sameMiddle
  · intro sameAB
    cases sameAB
    rfl

end BEDC.FKernel.Cont
