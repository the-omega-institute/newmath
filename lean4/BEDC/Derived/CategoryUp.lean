import BEDC.FKernel.Unary
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
namespace BEDC.Derived.CategoryUp
open BEDC.FKernel.Hist BEDC.FKernel.Cont BEDC.FKernel.Unary
def CategoryHomCarrier (a b f : BHist) : Prop :=
  UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory f ∧ Cont a f b
theorem CategoryHomCarrier_empty_identity {h : BHist} :
    UnaryHistory h -> CategoryHomCarrier h h BHist.Empty := by
  intro carrier
  exact And.intro carrier (And.intro carrier (And.intro unary_empty (cont_right_unit h)))
theorem CategoryHomCarrier_empty_identity_iff {a b : BHist} :
    CategoryHomCarrier a b BHist.Empty ↔ UnaryHistory a ∧ UnaryHistory b ∧ hsame a b := by
  constructor
  · intro homCarrier
    exact ⟨homCarrier.left, homCarrier.right.left,
      hsame_symm (cont_deterministic homCarrier.right.right.right (cont_right_unit a))⟩
  · intro data
    exact ⟨data.left, data.right.left, unary_empty,
      cont_result_hsame_transport (cont_right_unit a) data.right.right⟩
theorem CategoryHomCarrier_empty_morphism_endpoint_iff {a b : BHist} : CategoryHomCarrier a b BHist.Empty <-> UnaryHistory a /\ hsame a b :=
  ⟨fun h => ⟨(CategoryHomCarrier_empty_identity_iff.mp h).left,
    (CategoryHomCarrier_empty_identity_iff.mp h).right.right⟩,
    fun h => CategoryHomCarrier_empty_identity_iff.mpr
      ⟨h.left, unary_transport h.left h.right, h.right⟩⟩
theorem CategoryHomCarrier_empty_source_iff {b f : BHist} :
    CategoryHomCarrier BHist.Empty b f ↔ UnaryHistory b ∧ hsame f b := by
  constructor
  · intro homCarrier
    cases homCarrier with
    | intro _sourceCarrier rest =>
        cases rest with
        | intro targetCarrier rest =>
            cases rest with
            | intro _morphismCarrier homCont =>
                exact And.intro targetCarrier (hsame_symm (cont_left_unit_result homCont))
  · intro data
    cases data with
    | intro targetCarrier sameMorphism =>
        exact And.intro unary_empty
          (And.intro targetCarrier
            (And.intro (unary_transport targetCarrier (hsame_symm sameMorphism))
              (Iff.mpr cont_left_unit_iff (hsame_symm sameMorphism))))
theorem CategoryHomCarrier_empty_target_iff {a f : BHist} :
    CategoryHomCarrier a BHist.Empty f <-> hsame a BHist.Empty /\ hsame f BHist.Empty := by
  constructor
  · intro homCarrier
    have emptyParts := cont_empty_result_inversion homCarrier.right.right.right
    exact And.intro emptyParts.left emptyParts.right
  · intro parts
    cases parts with
    | intro sameA sameF =>
        cases sameA
        cases sameF
        exact And.intro unary_empty
          (And.intro unary_empty (And.intro unary_empty (cont_right_unit BHist.Empty)))
theorem CategoryHomCarrier_empty_source_empty_target_same_morphism_boundary {a b f : BHist} :
    CategoryHomCarrier BHist.Empty b f -> CategoryHomCarrier a BHist.Empty f ->
      hsame a BHist.Empty /\ hsame b BHist.Empty /\ hsame f BHist.Empty := by
  intro emptySource emptyTarget
  have sourceData := CategoryHomCarrier_empty_source_iff.mp emptySource
  have targetData := CategoryHomCarrier_empty_target_iff.mp emptyTarget
  exact And.intro targetData.left
    (And.intro (hsame_trans (hsame_symm sourceData.right) targetData.right) targetData.right)
theorem CategoryHomCarrier_comp_closed {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a c fg := by
  intro left right comp
  have sourceCarrier : UnaryHistory a := left.left
  have targetCarrier : UnaryHistory c := right.right.left
  have fCarrier : UnaryHistory f := left.right.right.left
  have gCarrier : UnaryHistory g := right.right.right.left
  cases left.right.right.right
  cases right.right.right.right
  cases comp
  exact And.intro sourceCarrier (And.intro targetCarrier
    (And.intro (unary_cont_closed fCarrier gCarrier (cont_intro rfl))
      (cont_intro (append_assoc a f g))))
theorem CategoryHomCarrier_comp_endpoint_cycle_morphism_empty {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      hsame a c -> hsame fg BHist.Empty := by
  intro left right comp sameEndpoint
  have composite : CategoryHomCarrier a c fg := CategoryHomCarrier_comp_closed left right comp
  exact cont_right_unit_unique
    (cont_result_hsame_transport composite.right.right.right (hsame_symm sameEndpoint))
theorem CategoryHomCarrier_identity_square_closed {a b f left right : BHist} :
    CategoryHomCarrier a b f -> Cont BHist.Empty f left -> Cont f BHist.Empty right ->
      CategoryHomCarrier a b left ∧ CategoryHomCarrier a b right ∧ hsame left right := by
  intro homCarrier leftRel rightRel
  have leftSame : hsame left f := cont_left_unit_result leftRel
  have rightSame : hsame right f := cont_deterministic rightRel (cont_right_unit f)
  have leftCarrier : CategoryHomCarrier a b left := by cases leftSame; exact homCarrier
  have rightCarrier : CategoryHomCarrier a b right := by cases rightSame; exact homCarrier
  exact And.intro leftCarrier (And.intro rightCarrier (leftSame.trans rightSame.symm))
theorem CategoryHomCarrier_comp_assoc_closed {a b c d f g h fg gh left right : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> CategoryHomCarrier c d h ->
      Cont f g fg -> Cont g h gh -> Cont fg h left -> Cont f gh right ->
        CategoryHomCarrier a d left ∧ CategoryHomCarrier a d right ∧ hsame left right := by
  intro first second third fgRel ghRel leftRel rightRel
  have fgCarrier : CategoryHomCarrier a c fg := CategoryHomCarrier_comp_closed first second fgRel
  have ghCarrier : CategoryHomCarrier b d gh := CategoryHomCarrier_comp_closed second third ghRel
  exact And.intro (CategoryHomCarrier_comp_closed fgCarrier third leftRel)
    (And.intro (CategoryHomCarrier_comp_closed first ghCarrier rightRel)
      (cont_assoc_hsame fgRel leftRel ghRel rightRel))
theorem CategoryHomCarrier_comp_assoc_displayed_deterministic
    {a b c d f g h fg gh left right displayed : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> CategoryHomCarrier c d h ->
      Cont f g fg -> Cont g h gh -> Cont fg h left -> Cont f gh right ->
        CategoryHomCarrier a d displayed -> hsame left displayed ∧ hsame right displayed := by
  intro first second third fgRel ghRel leftRel rightRel displayedCarrier
  exact
    let closed := CategoryHomCarrier_comp_assoc_closed first second third fgRel ghRel leftRel rightRel
    And.intro (cont_left_cancel closed.left.right.right.right displayedCarrier.right.right.right)
      (cont_left_cancel closed.right.left.right.right.right displayedCarrier.right.right.right)
theorem CategoryHomCarrier_morphism_deterministic {a b f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier a b g -> hsame f g := by
  intro left right; exact cont_left_cancel left.right.right.right right.right.right.right
theorem CategoryHomCarrier_endpoint_hsame_morphism_deterministic {a a' b b' f g : BHist} :
    hsame a a' -> hsame b b' -> CategoryHomCarrier a b f ->
      CategoryHomCarrier a' b' g -> hsame f g := by
  intro sameSource sameTarget left right
  cases sameSource; cases sameTarget; exact CategoryHomCarrier_morphism_deterministic left right
theorem CategoryHomCarrier_comp_public_readback {a b c f g fg : BHist} :
    CategoryHomCarrier a b f → CategoryHomCarrier b c g → Cont f g fg →
      CategoryHomCarrier a c fg ∧
        (∀ {fg' : BHist}, CategoryHomCarrier a c fg' → hsame fg fg') := by
  intro left right comp
  have compositeCarrier : CategoryHomCarrier a c fg := CategoryHomCarrier_comp_closed left right comp
  exact ⟨compositeCarrier, fun displayed =>
    CategoryHomCarrier_morphism_deterministic compositeCarrier displayed⟩
theorem CategoryHomCarrier_unary_suffix_iff {q a b f : BHist} :
    CategoryHomCarrier (append a q) (append b q) f <->
      UnaryHistory q /\ CategoryHomCarrier a b f := by
  constructor
  · intro homCarrier
    have qCarrier : UnaryHistory q := unary_append_right_factor homCarrier.left
    have aCarrier : UnaryHistory a := unary_append_left_factor homCarrier.left
    have bCarrier : UnaryHistory b := unary_append_left_factor homCarrier.right.left
    have fCarrier : UnaryHistory f := homCarrier.right.right.left
    have baseCont : Cont a f b := by
      apply (cont_suffix_iff (a := a) (b := b) (f := f) (p := q)).mp
      exact cont_intro
        (homCarrier.right.right.right.trans
          ((append_assoc a q f).trans
            (congrArg (append a) (unary_append_comm qCarrier fCarrier))))
    exact And.intro qCarrier
      (And.intro aCarrier (And.intro bCarrier (And.intro fCarrier baseCont)))
  · intro suffixed
    have qCarrier : UnaryHistory q := suffixed.left
    have baseCarrier : CategoryHomCarrier a b f := suffixed.right
    exact And.intro (unary_append_closed baseCarrier.left qCarrier)
      (And.intro (unary_append_closed baseCarrier.right.left qCarrier)
        (And.intro baseCarrier.right.right.left
          (cont_intro
            ((congrArg (fun x => append x q) baseCarrier.right.right.right).trans
              ((append_assoc a f q).trans
                ((congrArg (append a)
                    (unary_append_comm qCarrier baseCarrier.right.right.left).symm).trans
                  (append_assoc a q f).symm))))))
theorem CategoryHomCarrier_unary_suffix_comp_public_readback {q a b c f g fg : BHist} :
    UnaryHistory q -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier (append a q) (append c q) fg ∧
        (forall {fg' : BHist}, CategoryHomCarrier (append a q) (append c q) fg' ->
          hsame fg fg') := by
  intro qCarrier left right comp
  have readback := CategoryHomCarrier_comp_public_readback left right comp
  constructor
  · exact CategoryHomCarrier_unary_suffix_iff.mpr (And.intro qCarrier readback.left)
  · intro fg' displayed
    exact readback.right (CategoryHomCarrier_unary_suffix_iff.mp displayed).right
theorem CategoryHomCarrier_target_deterministic {a b c f : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier a c f -> hsame b c := by
  intro left right
  exact cont_deterministic left.right.right.right right.right.right.right
theorem CategoryHomCarrier_comp_target_deterministic {a b c d f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier a d fg -> hsame c d := by
  intro left right comp displayed
  exact CategoryHomCarrier_target_deterministic
    (CategoryHomCarrier_comp_closed left right comp) displayed
theorem CategoryHomCarrier_comp_middle_object_deterministic {a b b' c f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b' c g -> Cont f g fg ->
      CategoryHomCarrier a c fg -> hsame b b' := by
  intro left right comp displayed
  have derivedRight : Cont b g c := by
    cases left.right.right.right
    cases comp
    cases displayed.right.right.right
    exact cont_intro (append_assoc a f g).symm
  exact cont_right_cancel derivedRight right.right.right.right
theorem CategoryHomCarrier_append_suffix_comp_middle_object_deterministic
    {q a b b' c f g fg : BHist} :
    CategoryHomCarrier (append a q) (append b q) f ->
      CategoryHomCarrier (append b' q) (append c q) g -> Cont f g fg ->
        CategoryHomCarrier (append a q) (append c q) fg -> hsame b b' := by
  intro left right comp displayed
  exact append_right_cancel
    (CategoryHomCarrier_comp_middle_object_deterministic left right comp displayed)
theorem CategoryHomCarrier_comp_right_factor {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> Cont f g fg -> CategoryHomCarrier a c fg ->
      CategoryHomCarrier b c g := by
  intro left comp displayed
  have gCarrier : UnaryHistory g :=
    unary_cont_right_factor comp displayed.right.right.left
  have rightCont : Cont b g c := by
    cases left.right.right.right
    cases comp
    cases displayed.right.right.right
    exact cont_intro (append_assoc a f g).symm
  exact And.intro left.right.left
    (And.intro displayed.right.left (And.intro gCarrier rightCont))
theorem CategoryHomCarrier_comp_canonical_middle_iff {a c f g fg : BHist} :
    Cont f g fg -> (CategoryHomCarrier a c fg <->
      CategoryHomCarrier a (append a f) f ∧ CategoryHomCarrier (append a f) c g) := by
  intro comp; constructor
  · intro displayed
    have fCarrier : UnaryHistory f := unary_cont_left_factor comp displayed.right.right.left
    let left : CategoryHomCarrier a (append a f) f :=
      ⟨displayed.left, ⟨unary_append_closed displayed.left fCarrier, ⟨fCarrier, cont_intro rfl⟩⟩⟩
    exact ⟨left, CategoryHomCarrier_comp_right_factor left comp displayed⟩
  · exact fun factors => CategoryHomCarrier_comp_closed factors.left factors.right comp
theorem CategoryHomCarrier_comp_right_factor_public_readback {a b c f g fg : BHist} :
    CategoryHomCarrier a b f -> Cont f g fg -> CategoryHomCarrier a c fg ->
      CategoryHomCarrier b c g ∧
        (∀ {g' : BHist}, Cont f g' fg -> CategoryHomCarrier b c g' -> hsame g g') := by
  intro left comp displayed
  exact ⟨CategoryHomCarrier_comp_right_factor left comp displayed,
    fun {_g'} comp' _right => cont_left_cancel comp comp'⟩
theorem CategoryHomCarrier_comp_left_factor {a b c f g fg : BHist} :
    CategoryHomCarrier b c g -> Cont f g fg -> CategoryHomCarrier a c fg ->
      CategoryHomCarrier a b f := by
  intro right comp displayed
  have fCarrier : UnaryHistory f :=
    unary_cont_left_factor comp displayed.right.right.left
  have leftCont : Cont a f b :=
    cont_composite_left_factor right.right.right.right comp displayed.right.right.right
  exact And.intro displayed.left
    (And.intro right.left (And.intro fCarrier leftCont))
theorem CategoryHomCarrier_comp_left_factor_public_readback {a b c f g fg : BHist} :
    CategoryHomCarrier b c g -> Cont f g fg -> CategoryHomCarrier a c fg ->
      CategoryHomCarrier a b f /\
        (forall {f' : BHist}, Cont f' g fg -> CategoryHomCarrier a b f' -> hsame f f') := by
  intro right comp displayed
  exact ⟨CategoryHomCarrier_comp_left_factor right comp displayed,
    fun {_f'} comp' _left => cont_right_cancel comp comp'⟩
theorem CategoryHomCarrier_source_deterministic {a b c f : BHist} :
    CategoryHomCarrier a c f -> CategoryHomCarrier b c f -> hsame a b := by
  intro left right
  exact cont_right_cancel left.right.right.right right.right.right.right
theorem CategoryHomCarrier_comp_source_deterministic {a b c d f g fg : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      CategoryHomCarrier d c fg -> hsame a d := by
  intro left right comp displayed
  exact CategoryHomCarrier_source_deterministic
    (CategoryHomCarrier_comp_closed left right comp) displayed
theorem CategoryHomCarrier_tail_comm_hsame {a b c f g fg gf : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      Cont g f gf -> hsame fg gf := by
  intro left right fgRel gfRel
  exact unary_continuation_commutativity left.2.2.1 right.2.2.1 fgRel gfRel
theorem CategoryHomCarrier_hsame_transport {a a' b b' f f' : BHist} :
    hsame a a' -> hsame b b' -> hsame f f' ->
      CategoryHomCarrier a b f -> CategoryHomCarrier a' b' f' := by
  intro sameSource sameTarget sameMorphism homCarrier
  cases sameSource; cases sameTarget; cases sameMorphism; exact homCarrier
theorem CategoryHomCarrier_endpoint_transport_cont_classified {a a' b b' f f' g : BHist} :
    hsame a a' -> hsame b b' -> hsame f f' -> CategoryHomCarrier a b f ->
      CategoryHomCarrier a' b' g -> Cont a' f' b' ∧ CategoryHomCarrier a' b' f' ∧
        hsame f' g := by
  intro sameSource sameTarget sameMorphism left right
  have moved := CategoryHomCarrier_hsame_transport sameSource sameTarget sameMorphism left
  exact And.intro moved.right.right.right
    (And.intro moved (CategoryHomCarrier_morphism_deterministic moved right))
theorem CategoryHomCarrier_e0_source_absurd {a target f : BHist} :
    CategoryHomCarrier (BHist.e0 a) target f → False :=
  fun homCarrier => unary_no_zero_extension homCarrier.left
theorem CategoryHomCarrier_e0_target_absurd {source a morph : BHist} :
    CategoryHomCarrier source (BHist.e0 a) morph -> False :=
  fun homCarrier => unary_no_zero_extension homCarrier.right.left
structure ContinuationMorphism (src tgt : BHist) where
  tail : BHist
  rel : Cont src tail tgt
theorem ContinuationMorphism_tail_deterministic {a b : BHist}
    (left right : ContinuationMorphism a b) : hsame left.tail right.tail := by
  exact cont_left_cancel left.rel right.rel
theorem ContinuationMorphism_source_deterministic {a b c : BHist}
    (left : ContinuationMorphism a c) (right : ContinuationMorphism b c) :
    hsame left.tail right.tail -> hsame a b := by
  intro sameTail
  cases left with | mk leftTail leftRel =>
    cases right with | mk rightTail rightRel =>
      cases sameTail
      exact cont_right_cancel leftRel rightRel
theorem ContinuationMorphism_target_deterministic {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism a c) :
    hsame left.tail right.tail -> hsame b c := by
  intro sameTail
  cases left with | mk leftTail leftRel =>
    cases right with | mk rightTail rightRel =>
      cases sameTail
      exact cont_deterministic leftRel rightRel
def ContinuationMorphism_comp_closed {a b c : BHist} (left : ContinuationMorphism a b)
    (right : ContinuationMorphism b c) : ContinuationMorphism a c := by
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          exact
            { tail := append leftTail rightTail
              rel := by
                cases leftRel
                exact rightRel.trans (append_assoc a leftTail rightTail) }
theorem ContinuationMorphism_comp_tail_nonempty_iff {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    ((hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty -> False) <->
      (hsame left.tail BHist.Empty -> False) ∨ (hsame right.tail BHist.Empty -> False)) := by
  cases left; cases right; exact BEDC.FKernel.Cont.append_nonempty_iff
theorem ContinuationMorphism_comp_tail_append_deterministic {a b c : BHist}
    (left left' : ContinuationMorphism a b) (right right' : ContinuationMorphism b c) :
    hsame (append left.tail right.tail) (append left'.tail right'.tail) := by
  exact (congrArg (fun tail => append tail right.tail)
    (ContinuationMorphism_tail_deterministic left left')).trans
      (congrArg (append left'.tail) (ContinuationMorphism_tail_deterministic right right'))
theorem ContinuationMorphism_comp_empty_target_inversion {a b : BHist} (left : ContinuationMorphism a b) (right : ContinuationMorphism b BHist.Empty) : hsame a BHist.Empty ∧ hsame b BHist.Empty ∧ hsame left.tail BHist.Empty ∧ hsame right.tail BHist.Empty := by
  cases left with | mk leftTail leftRel => cases right with | mk rightTail rightRel =>
  exact let rp := cont_empty_result_inversion rightRel; let lp := cont_empty_result_inversion (show Cont a leftTail BHist.Empty from by cases rp.left; exact leftRel); ⟨lp.left, rp.left, lp.right, rp.right⟩
theorem ContinuationMorphism_comp_tail_nonempty_target_not_empty {a b c : BHist} (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) : (hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty -> False) -> hsame c BHist.Empty -> False := by
  intro nonempty sameTarget; have inv := ContinuationMorphism_comp_empty_target_inversion left { tail := right.tail, rel := cont_result_hsame_transport right.rel sameTarget }; exact (Iff.mp (ContinuationMorphism_comp_tail_nonempty_iff left right) nonempty).elim (fun h => h inv.right.right.left) (fun h => h inv.right.right.right)
theorem ContinuationMorphism_comp_endpoint_cycle_tail_empty {a b c : BHist}
    (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) :
    hsame a c -> hsame (ContinuationMorphism_comp_closed left right).tail BHist.Empty := by
  intro sameEndpoint
  exact cont_right_unit_unique
    (cont_result_hsame_transport
      (ContinuationMorphism_comp_closed left right).rel (hsame_symm sameEndpoint))
theorem ContinuationMorphism_comp_endpoint_cycle_boundary {a b c : BHist} (left : ContinuationMorphism a b) (right : ContinuationMorphism b c) : hsame a c -> hsame left.tail BHist.Empty ∧ hsame right.tail BHist.Empty ∧ hsame a b ∧ hsame b c := by
  intro sameEndpoint; cases left with | mk leftTail leftRel => cases right with | mk rightTail rightRel =>
    exact let tails := cont_mutual_extension_tails_empty leftRel (cont_result_hsame_transport rightRel (hsame_symm sameEndpoint)); ⟨tails.left, tails.right, cont_deterministic (cont_right_unit a) (cont_hsame_transport (hsame_refl a) tails.left (hsame_refl b) leftRel), cont_deterministic (cont_right_unit b) (cont_hsame_transport (hsame_refl b) tails.right (hsame_refl c) rightRel)⟩
theorem ContinuationMorphism_identity_tail_hsame {a b : BHist}
    (m : ContinuationMorphism a b) :
    hsame (ContinuationMorphism_comp_closed { tail := BHist.Empty, rel := cont_right_unit a } m).tail
        m.tail /\
      hsame (ContinuationMorphism_comp_closed m { tail := BHist.Empty, rel := cont_right_unit b }).tail
        m.tail := by
  cases m with | mk tail rel => exact And.intro (append_empty_left tail) (append_empty_right tail)
theorem ContinuationMorphism_identity_comp_closure :
    (forall h : BHist, Nonempty (ContinuationMorphism h h)) ∧
      (forall {a b c : BHist}, ContinuationMorphism a b ->
        ContinuationMorphism b c -> Nonempty (ContinuationMorphism a c)) := by
  exact ⟨fun h => Nonempty.intro { tail := BHist.Empty, rel := cont_right_unit h },
    fun {_a _b _c : BHist} left right =>
      Nonempty.intro (ContinuationMorphism_comp_closed left right)⟩
theorem ContinuationMorphism_comp_assoc_closed {a b c d : BHist}
    (first : ContinuationMorphism a b) (second : ContinuationMorphism b c)
    (third : ContinuationMorphism c d) :
    ∃ left : ContinuationMorphism a d, ∃ right : ContinuationMorphism a d,
      hsame left.tail right.tail := by
  cases first with
  | mk firstTail firstRel =>
      cases second with
      | mk secondTail secondRel =>
          cases third with
          | mk thirdTail thirdRel =>
              refine Exists.intro
                { tail := append (append firstTail secondTail) thirdTail, rel := ?_ }
                (Exists.intro
                  { tail := append firstTail (append secondTail thirdTail), rel := ?_ } ?_)
              · cases firstRel
                cases secondRel
                cases thirdRel
                exact (append_assoc (append a firstTail) secondTail thirdTail).trans
                  ((append_assoc a firstTail (append secondTail thirdTail)).trans
                    (congrArg (append a) (append_assoc firstTail secondTail thirdTail).symm))
              · cases firstRel
                cases secondRel
                cases thirdRel
                exact (append_assoc (append a firstTail) secondTail thirdTail).trans
                  (append_assoc a firstTail (append secondTail thirdTail))
              · exact append_assoc firstTail secondTail thirdTail
theorem ContinuationMorphism_comp_assoc_tail_hsame {a b c d : BHist}
    (first : ContinuationMorphism a b) (second : ContinuationMorphism b c)
    (third : ContinuationMorphism c d) :
    hsame (ContinuationMorphism_comp_closed (ContinuationMorphism_comp_closed first second)
        third).tail
      (ContinuationMorphism_comp_closed first
        (ContinuationMorphism_comp_closed second third)).tail := by
  cases first
  cases second
  cases third
  exact append_assoc _ _ _
def ContinuationMorphism_comp_right_factor {a b c rightTail : BHist}
    (left : ContinuationMorphism a b) (composite : ContinuationMorphism a c) :
    Cont left.tail rightTail composite.tail -> ContinuationMorphism b c := by
  intro tailRel
  cases left with
  | mk leftTail leftRel =>
      cases composite with
      | mk compositeTail compositeRel =>
          refine { tail := rightTail, rel := ?_ }
          cases leftRel
          cases tailRel
          cases compositeRel
          exact cont_intro (append_assoc a leftTail rightTail).symm
def ContinuationMorphism_comp_left_factor {a b c leftTail : BHist}
    (right : ContinuationMorphism b c) (composite : ContinuationMorphism a c) :
    Cont leftTail right.tail composite.tail -> ContinuationMorphism a b := by
  intro tailRel
  cases right with
  | mk rightTail rightRel =>
      cases composite with
      | mk compositeTail compositeRel =>
          refine { tail := leftTail, rel := ?_ }
          exact cont_composite_left_factor rightRel tailRel compositeRel
theorem category_cont_left_e0_result_cases {h k r : BHist} :
    Cont (BHist.e0 h) k (BHist.e0 r) ->
      (k = BHist.Empty ∧ hsame h r) ∨
        (∃ k0 : BHist, k = BHist.e0 k0 ∧ Cont (BHist.e0 h) k0 r) := by
  intro hcont
  cases k with
  | Empty =>
      left
      constructor
      · rfl
      · exact (BHist.e0.inj hcont).symm
  | e0 k0 =>
      right
      exact Exists.intro k0 (And.intro rfl (BHist.e0.inj hcont))
  | e1 k0 =>
      cases hcont
theorem CategoryHomCarrier_left_e1_result_cases {a k r : BHist} :
    CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) k ->
      (k = BHist.Empty /\ UnaryHistory a /\ hsame a r) \/
        (exists k0 : BHist, k = BHist.e1 k0 /\ UnaryHistory k0 /\
          Cont (BHist.e1 a) k0 r) := by
  intro homCarrier
  cases homCarrier with
  | intro sourceCarrier rest =>
      cases rest with
      | intro _targetCarrier rest =>
          cases rest with
          | intro morphCarrier homCont =>
              cases k with
              | Empty =>
                  exact Or.inl
                    (And.intro rfl
                      (And.intro (unary_e1_inversion sourceCarrier)
                        (BHist.e1.inj homCont).symm))
              | e0 k0 =>
                  cases homCont
              | e1 k0 =>
                  exact Or.inr
                    (Exists.intro k0
                      (And.intro rfl
                        (And.intro (unary_e1_inversion morphCarrier)
                          (BHist.e1.inj homCont))))
theorem CategoryHomCarrier_e1_source_e1_target_nonempty_morphism_cases {a r morph : BHist} :
    CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) morph ->
      (hsame morph BHist.Empty -> False) ->
        exists k : BHist, morph = BHist.e1 k /\ UnaryHistory a /\ UnaryHistory k /\
          UnaryHistory r /\ Cont (BHist.e1 a) k r := by
  intro homCarrier nonempty
  have targetCarrier : UnaryHistory r := unary_e1_inversion homCarrier.right.left
  cases CategoryHomCarrier_left_e1_result_cases homCarrier with
  | inl emptyCase =>
      exact False.elim (nonempty (by cases emptyCase.left; exact hsame_refl BHist.Empty))
  | inr visibleCase =>
      cases visibleCase with
      | intro k data =>
          exact Exists.intro k
            (And.intro data.left
              (And.intro (unary_e1_inversion homCarrier.left)
                (And.intro data.right.left (And.intro targetCarrier data.right.right))))
theorem CategoryHomCarrier_e1_target_nonempty_morphism_source_cases {source r morph : BHist} :
    CategoryHomCarrier source (BHist.e1 r) morph -> (hsame morph BHist.Empty -> False) ->
      (source = BHist.Empty ∧ morph = BHist.e1 r ∧ UnaryHistory r) ∨
        (∃ a k : BHist, source = BHist.e1 a ∧ morph = BHist.e1 k ∧
          UnaryHistory a ∧ UnaryHistory k ∧ UnaryHistory r ∧ Cont (BHist.e1 a) k r) := by
  intro homCarrier nonempty
  cases source with
  | Empty =>
      cases morph with
      | Empty => cases homCarrier.right.right.right
      | e0 k => cases homCarrier.right.right.right
      | e1 k =>
          left
          have sameTail : k = r :=
            ((BHist.e1.inj homCarrier.right.right.right).trans (append_empty_left k)).symm
          exact ⟨rfl, congrArg BHist.e1 sameTail, unary_e1_inversion homCarrier.right.left⟩
  | e0 a => exact False.elim (CategoryHomCarrier_e0_source_absurd homCarrier)
  | e1 a =>
      right
      cases CategoryHomCarrier_e1_source_e1_target_nonempty_morphism_cases homCarrier nonempty with
      | intro k data =>
          exact ⟨a, k, rfl, data.left, data.right.left, data.right.right.left,
            data.right.right.right.left, data.right.right.right.right⟩
theorem CategoryHomCarrier_e1_morphism_target_iff {a k r : BHist} :
    CategoryHomCarrier a (BHist.e1 r) (BHist.e1 k) <->
      UnaryHistory a ∧ UnaryHistory k ∧ Cont a k r := by
  constructor
  · intro homCarrier
    exact And.intro homCarrier.left
      (And.intro (unary_e1_inversion homCarrier.right.right.left)
        (BHist.e1.inj homCarrier.right.right.right))
  · intro data
    exact And.intro data.left
      (And.intro (unary_e1_closed
          (unary_cont_closed data.left data.right.left data.right.right))
        (And.intro (unary_e1_closed data.right.left) (cont_step_one data.right.right)))
theorem CategoryHomCarrier_e1_target_morphism_exactness {a k r : BHist} :
    CategoryHomCarrier a (BHist.e1 r) (BHist.e1 k) → CategoryHomCarrier a r k := by
  intro homCarrier
  have data := (CategoryHomCarrier_e1_morphism_target_iff.mp homCarrier)
  exact And.intro data.left
    (And.intro (unary_e1_inversion homCarrier.right.left)
      (And.intro data.right.left data.right.right))
theorem CategoryHomCarrier_e1_source_e1_morphism_target_iff {a k target : BHist} :
    CategoryHomCarrier (BHist.e1 a) target (BHist.e1 k) <->
      exists r : BHist, target = BHist.e1 r /\ UnaryHistory a /\ UnaryHistory k /\
        UnaryHistory r /\ Cont (BHist.e1 a) k r := by
  constructor
  · intro homCarrier
    cases homCarrier with
    | intro sourceCarrier rest =>
        cases rest with
        | intro targetCarrier rest =>
            cases rest with
            | intro morphCarrier homCont =>
                cases target with
                | Empty =>
                    cases homCont
                | e0 r =>
                    cases homCont
                | e1 r =>
                    exact Exists.intro r
                      (And.intro rfl
                        (And.intro (unary_e1_inversion sourceCarrier)
                          (And.intro (unary_e1_inversion morphCarrier)
                            (And.intro (unary_e1_inversion targetCarrier)
                              (BHist.e1.inj homCont)))))
  · intro witness
    cases witness with
    | intro r data =>
        cases data with
        | intro targetEq rest =>
            cases rest with
            | intro sourceCarrier rest =>
                cases rest with
                | intro morphCarrier rest =>
                    cases rest with
                    | intro targetCarrier homCont =>
                        cases targetEq
                        exact And.intro (unary_e1_closed sourceCarrier)
                          (And.intro (unary_e1_closed targetCarrier)
                            (And.intro (unary_e1_closed morphCarrier)
                              (cont_step_one homCont)))
theorem CategoryHomCarrier_e1_source_empty_target_absurd {a f : BHist} :
    CategoryHomCarrier (BHist.e1 a) BHist.Empty f -> False := by
  intro homCarrier
  cases f <;> cases homCarrier.right.right.right
theorem CategoryHomCarrier_visible_source_empty_target_comp_absurd {a b f g : BHist} : CategoryHomCarrier (BHist.e1 a) b f -> CategoryHomCarrier b BHist.Empty g -> False := by
  intro left right; exact CategoryHomCarrier_e1_source_empty_target_absurd (CategoryHomCarrier_comp_closed left right (cont_intro rfl))
theorem CategoryHomCarrier_e1_source_morphism_cases {a target morph : BHist} :
    CategoryHomCarrier (BHist.e1 a) target morph ->
      (morph = BHist.Empty /\ target = BHist.e1 a /\ UnaryHistory a) \/
        (exists k r : BHist, morph = BHist.e1 k /\ target = BHist.e1 r /\
          UnaryHistory a /\ UnaryHistory k /\ UnaryHistory r /\ Cont (BHist.e1 a) k r) := by
  intro homCarrier
  cases morph with
  | Empty => left; exact ⟨rfl, homCarrier.right.right.right, unary_e1_inversion homCarrier.left⟩
  | e0 k => exact False.elim (unary_no_zero_extension homCarrier.right.right.left)
  | e1 k =>
      right
      cases target with
      | Empty => cases homCarrier.right.right.right
      | e0 r => cases homCarrier.right.right.right
      | e1 r =>
          exact ⟨k, r, rfl, rfl, unary_e1_inversion homCarrier.left,
            unary_e1_inversion homCarrier.right.right.left, unary_e1_inversion homCarrier.right.left,
            BHist.e1.inj homCarrier.right.right.right⟩
theorem CategoryHomCarrier_e1_source_nonempty_morphism_target_cases {a target morph : BHist} :
    CategoryHomCarrier (BHist.e1 a) target morph -> (hsame morph BHist.Empty -> False) ->
      exists k r : BHist, morph = BHist.e1 k /\ target = BHist.e1 r /\
        UnaryHistory a /\ UnaryHistory k /\ UnaryHistory r /\ Cont (BHist.e1 a) k r := by
  intro homCarrier nonempty
  cases CategoryHomCarrier_e1_source_morphism_cases homCarrier with
  | inl emptyCase => cases emptyCase.left; exact False.elim (nonempty (hsame_refl BHist.Empty))
  | inr visibleCase => exact visibleCase
theorem CategoryHomCarrier_identity_semanticNameCert {a : BHist} :
    UnaryHistory a ->
      BEDC.FKernel.NameCert.SemanticNameCert (CategoryHomCarrier a a)
        (CategoryHomCarrier a a) (CategoryHomCarrier a a) hsame := by
  intro carrier
  exact ⟨⟨Exists.intro BHist.Empty (CategoryHomCarrier_empty_identity carrier),
    (fun {h : BHist} (_ : CategoryHomCarrier a a h) => hsame_refl h),
    (fun {_ _ : BHist} same => hsame_symm same),
    (fun {_ _ _ : BHist} sameHK sameKR => hsame_trans sameHK sameKR),
    (fun {_ _ : BHist} same homCarrier => by cases same; exact homCarrier)⟩,
    (fun {_ : BHist} source => source), (fun {_ : BHist} source => source)⟩
theorem CategoryHomCarrier_endomorphism_empty_iff {a f : BHist} : CategoryHomCarrier a a f ↔ UnaryHistory a ∧ hsame f BHist.Empty :=
  ⟨fun h => ⟨h.left, cont_right_unit_unique h.right.right.right⟩,
    fun h => by cases h.right; exact CategoryHomCarrier_empty_identity h.left⟩
end BEDC.Derived.CategoryUp
