import BEDC.Derived.NatTransUp
import BEDC.Derived.CategoryUp.CompResultNonemptySourceTargetCases

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem NatTransPrefixComponentCarrier_vert_comp_nonempty_result_target_visible
    {p q r a eta theta k : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta (BHist.e1 k) ->
        ∃ s : BHist, append r a = BHist.e1 s ∧ UnaryHistory k ∧ UnaryHistory s ∧
          Cont (append p a) (BHist.e1 k) (BHist.e1 s) := by
  intro left right comp
  have casesData :=
    CategoryHomCarrier_comp_result_nonempty_source_target_cases
      left.right.right.right right.right.right.right comp
      (fun sameEmpty => not_hsame_e1_empty sameEmpty)
  cases casesData with
  | inl emptySource =>
      cases emptySource.right with
      | intro k' targetData =>
          cases targetData with
          | intro s data =>
              cases data.left
              exact Exists.intro s data.right
  | inr visibleSource =>
      cases visibleSource with
      | intro sourceTail sourceData =>
          cases sourceData with
          | intro k' targetData =>
              cases targetData with
              | intro s data =>
                  cases data.right.left
                  have sourceSame : hsame (BHist.e1 sourceTail) (append p a) := by
                    exact data.left.symm
                  have sourceRel : Cont (append p a) (BHist.e1 k) (BHist.e1 s) :=
                    cont_hsame_transport sourceSame (hsame_refl (BHist.e1 k))
                      (hsame_refl (BHist.e1 s)) data.right.right.right.right.right.right
                  exact Exists.intro s
                    (And.intro data.right.right.left
                      (And.intro data.right.right.right.right.left
                        (And.intro data.right.right.right.right.right.left sourceRel)))

theorem NatTransPrefixComponentCarrier_vert_comp_nonempty_result_source_visible
    {p q r a eta theta k : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta (BHist.e1 k) ->
        (hsame (append p a) BHist.Empty -> False) ->
          ∃ s t : BHist, append p a = BHist.e1 s ∧ append r a = BHist.e1 t ∧
            UnaryHistory s ∧ UnaryHistory k ∧ UnaryHistory t ∧
              Cont (BHist.e1 s) (BHist.e1 k) (BHist.e1 t) := by
  intro left right comp sourceNonempty
  have casesData :=
    CategoryHomCarrier_comp_result_nonempty_source_target_cases
      left.right.right.right right.right.right.right comp
      (fun sameEmpty => not_hsame_e1_empty sameEmpty)
  cases casesData with
  | inl emptySource =>
      exact False.elim (sourceNonempty emptySource.left)
  | inr visibleSource =>
      cases visibleSource with
      | intro s dataS =>
          cases dataS with
          | intro k1 dataK =>
              cases dataK with
              | intro t data =>
                  cases data.right.left
                  exact Exists.intro s
                    (Exists.intro t
                      (And.intro data.left
                        (And.intro data.right.right.left
                          (And.intro data.right.right.right.left
                            (And.intro data.right.right.right.right.left
                              (And.intro data.right.right.right.right.right.left
                                data.right.right.right.right.right.right))))))

theorem NatTransPrefixComponentCarrier_vert_comp_nonempty_result_source_target_cases
    {p q r a eta theta k : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta (BHist.e1 k) ->
        (hsame (append p a) BHist.Empty ∧
          ∃ t : BHist, append r a = BHist.e1 t ∧ UnaryHistory k ∧ UnaryHistory t ∧
            Cont (append p a) (BHist.e1 k) (BHist.e1 t)) ∨
          (∃ s t : BHist, append p a = BHist.e1 s ∧ append r a = BHist.e1 t ∧
            UnaryHistory s ∧ UnaryHistory k ∧ UnaryHistory t ∧
              Cont (BHist.e1 s) (BHist.e1 k) (BHist.e1 t)) := by
  intro left right comp
  have casesData :=
    CategoryHomCarrier_comp_result_nonempty_source_target_cases
      left.right.right.right right.right.right.right comp
      (fun sameEmpty => not_hsame_e1_empty sameEmpty)
  cases casesData with
  | inl emptySource =>
      cases emptySource.right with
      | intro k' targetData =>
          cases targetData with
          | intro t data =>
              cases data.left
              left
              exact And.intro emptySource.left
                (Exists.intro t data.right)
  | inr visibleSource =>
      cases visibleSource with
      | intro s sourceData =>
          cases sourceData with
          | intro k' targetData =>
              cases targetData with
              | intro t data =>
                  cases data.right.left
                  right
                  exact Exists.intro s
                    (Exists.intro t
                      (And.intro data.left
                        (And.intro data.right.right.left
                          (And.intro data.right.right.right.left
                            (And.intro data.right.right.right.right.left
                              (And.intro data.right.right.right.right.right.left
                                data.right.right.right.right.right.right))))))

theorem NatTransPrefixComponentCarrier_vert_comp_nonempty_result_right_identity_visible_readback
    {p q r a eta theta k right : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta (BHist.e1 k) ->
        Cont (BHist.e1 k) BHist.Empty right ->
          (hsame (append p a) BHist.Empty -> False) ->
            NatTransPrefixComponentCarrier p r a right ∧ hsame right (BHist.e1 k) ∧
              ∃ s t : BHist, append p a = BHist.e1 s ∧ append r a = BHist.e1 t ∧
                UnaryHistory s ∧ UnaryHistory k ∧ UnaryHistory t ∧
                  Cont (BHist.e1 s) (BHist.e1 k) (BHist.e1 t) := by
  intro left component comp rightRel sourceNonempty
  have compositeCarrier : NatTransPrefixComponentCarrier p r a (BHist.e1 k) :=
    NatTransPrefixComponentCarrier_vert_comp_closed left component comp
  have rightClosed :=
    NatTransPrefixComponentCarrier_vert_comp_right_identity_closed compositeCarrier rightRel
  have visibleReadback :=
    NatTransPrefixComponentCarrier_vert_comp_nonempty_result_source_visible left component comp
      sourceNonempty
  exact And.intro rightClosed.left (And.intro rightClosed.right visibleReadback)

theorem NatTransPrefixComponentCarrier_vert_comp_nonempty_result_left_identity_visible_readback
    {p q r a eta theta k leftResult : BHist} :
    NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentCarrier q r a theta -> Cont eta theta (BHist.e1 k) ->
        Cont BHist.Empty (BHist.e1 k) leftResult ->
          (hsame (append p a) BHist.Empty -> False) ->
            NatTransPrefixComponentCarrier p r a leftResult ∧ hsame leftResult (BHist.e1 k) ∧
              ∃ s t : BHist, append p a = BHist.e1 s ∧ append r a = BHist.e1 t ∧
                UnaryHistory s ∧ UnaryHistory k ∧ UnaryHistory t ∧
                  Cont (BHist.e1 s) (BHist.e1 k) (BHist.e1 t) := by
  intro left component comp leftRel sourceNonempty
  have compositeCarrier : NatTransPrefixComponentCarrier p r a (BHist.e1 k) :=
    NatTransPrefixComponentCarrier_vert_comp_closed left component comp
  have leftClosed :=
    NatTransPrefixComponentCarrier_vert_comp_left_identity_closed compositeCarrier leftRel
  have visibleReadback :=
    NatTransPrefixComponentCarrier_vert_comp_nonempty_result_source_visible left component comp
      sourceNonempty
  exact And.intro leftClosed.left (And.intro leftClosed.right visibleReadback)

end BEDC.Derived.NatTransUp
