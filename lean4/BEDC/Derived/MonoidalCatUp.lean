import BEDC.Derived.CategoryUp
import BEDC.FKernel.Unary.Commutativity

namespace BEDC.Derived.MonoidalCatUp

open BEDC.Derived.CategoryUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def MonoidalCatSingletonTensor (h k : BHist) : BHist := append h k

theorem MonoidalCatSingleton_tensor_identity_hom {a b : BHist} :
    UnaryHistory a ->
      UnaryHistory b ->
        hsame (MonoidalCatSingletonTensor BHist.Empty BHist.Empty) BHist.Empty ∧
          CategoryHomCarrier (append a b) (append a b) BHist.Empty := by
  intro leftCarrier rightCarrier
  have tensorCarrier : UnaryHistory (append a b) :=
    unary_append_closed leftCarrier rightCarrier
  exact And.intro rfl (CategoryHomCarrier_empty_identity tensorCarrier)

theorem MonoidalCatSingleton_tensor_carrier {a b c d f g : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier c d g ->
      UnaryHistory (append a c) ∧
        CategoryHomCarrier (append a c) (append b d) (append f g) := by
  intro left right
  have sourceCarrier : UnaryHistory (append a c) :=
    unary_append_closed left.left right.left
  have targetCarrier : UnaryHistory (append b d) :=
    unary_append_closed left.right.left right.right.left
  have morphismCarrier : UnaryHistory (append f g) :=
    unary_append_closed left.right.right.left right.right.right.left
  have targetEq :
      append (append a c) (append f g) = append b d := by
    calc
      append (append a c) (append f g)
          = append a (append c (append f g)) :=
            append_assoc a c (append f g)
      _ = append a (append (append c f) g) :=
            congrArg (append a) (append_assoc c f g).symm
      _ = append a (append (append f c) g) :=
            congrArg (fun x => append a (append x g))
              (unary_append_comm right.left left.right.right.left)
      _ = append a (append f (append c g)) :=
            congrArg (append a) (append_assoc f c g)
      _ = append (append a f) (append c g) :=
            (append_assoc a f (append c g)).symm
      _ = append b (append c g) :=
            congrArg (fun x => append x (append c g)) left.right.right.right.symm
      _ = append b d :=
            congrArg (append b) right.right.right.right.symm
  exact And.intro sourceCarrier
    (And.intro sourceCarrier
      (And.intro targetCarrier
        (And.intro morphismCarrier (cont_intro targetEq.symm))))

theorem MonoidalCatSingleton_associator_unitors {x y z left right leftUnit rightUnit :
    BHist} :
    UnaryHistory x ->
      UnaryHistory y ->
        UnaryHistory z ->
          Cont (append x y) z left ->
            Cont x (append y z) right ->
              Cont BHist.Empty x leftUnit ->
                Cont x BHist.Empty rightUnit ->
                  CategoryHomCarrier (append (append x y) z) (append x (append y z))
                      BHist.Empty ∧
                    CategoryHomCarrier (append BHist.Empty x) x BHist.Empty ∧
                      CategoryHomCarrier (append x BHist.Empty) x BHist.Empty ∧
                        hsame left right ∧ hsame leftUnit x ∧ hsame rightUnit x := by
  intro xUnary yUnary zUnary leftCont rightCont leftUnitCont rightUnitCont
  have assocSourceUnary : UnaryHistory (append (append x y) z) :=
    unary_append_closed (unary_append_closed xUnary yUnary) zUnary
  have assocTargetUnary : UnaryHistory (append x (append y z)) :=
    unary_append_closed xUnary (unary_append_closed yUnary zUnary)
  have assocSame : hsame (append (append x y) z) (append x (append y z)) :=
    append_assoc x y z
  have assocHom :
      CategoryHomCarrier (append (append x y) z) (append x (append y z)) BHist.Empty :=
    CategoryHomCarrier_empty_identity_iff.mpr
      (And.intro assocSourceUnary (And.intro assocTargetUnary assocSame))
  have leftUnitSourceUnary : UnaryHistory (append BHist.Empty x) :=
    unary_append_closed unary_empty xUnary
  have leftUnitSame : hsame (append BHist.Empty x) x :=
    append_empty_left x
  have leftUnitHom : CategoryHomCarrier (append BHist.Empty x) x BHist.Empty :=
    CategoryHomCarrier_empty_identity_iff.mpr
      (And.intro leftUnitSourceUnary (And.intro xUnary leftUnitSame))
  have rightUnitSourceUnary : UnaryHistory (append x BHist.Empty) :=
    unary_append_closed xUnary unary_empty
  have rightUnitSame : hsame (append x BHist.Empty) x :=
    append_empty_right x
  have rightUnitHom : CategoryHomCarrier (append x BHist.Empty) x BHist.Empty :=
    CategoryHomCarrier_empty_identity_iff.mpr
      (And.intro rightUnitSourceUnary (And.intro xUnary rightUnitSame))
  exact And.intro assocHom
    (And.intro leftUnitHom
      (And.intro rightUnitHom
        (And.intro
          (cont_assoc_hsame (cont_intro rfl) leftCont (cont_intro rfl) rightCont)
          (And.intro (cont_left_unit_result leftUnitCont)
            (cont_deterministic rightUnitCont (cont_right_unit x))))))

theorem MonoidalCatSingleton_tensor_preserves_composition
    {a0 a1 a2 c0 c1 c2 f fPrime g gPrime : BHist} :
    CategoryHomCarrier a0 a1 f ->
      CategoryHomCarrier a1 a2 fPrime ->
        CategoryHomCarrier c0 c1 g ->
          CategoryHomCarrier c1 c2 gPrime ->
            CategoryHomCarrier (append a0 c0) (append a2 c2)
                (append (append f g) (append fPrime gPrime)) ∧
              CategoryHomCarrier (append a0 c0) (append a2 c2)
                (append (append f fPrime) (append g gPrime)) ∧
                hsame (append (append f g) (append fPrime gPrime))
                  (append (append f fPrime) (append g gPrime)) := by
  intro fCarrier fPrimeCarrier gCarrier gPrimeCarrier
  have fgTensor :
      CategoryHomCarrier (append a0 c0) (append a1 c1) (append f g) :=
    (MonoidalCatSingleton_tensor_carrier fCarrier gCarrier).right
  have fPrimeGPrimeTensor :
      CategoryHomCarrier (append a1 c1) (append a2 c2) (append fPrime gPrime) :=
    (MonoidalCatSingleton_tensor_carrier fPrimeCarrier gPrimeCarrier).right
  have tensorThenComposite :
      CategoryHomCarrier (append a0 c0) (append a2 c2)
        (append (append f g) (append fPrime gPrime)) :=
    CategoryHomCarrier_comp_closed fgTensor fPrimeGPrimeTensor (cont_intro rfl)
  have fThenFPrime :
      CategoryHomCarrier a0 a2 (append f fPrime) :=
    CategoryHomCarrier_comp_closed fCarrier fPrimeCarrier (cont_intro rfl)
  have gThenGPrime :
      CategoryHomCarrier c0 c2 (append g gPrime) :=
    CategoryHomCarrier_comp_closed gCarrier gPrimeCarrier (cont_intro rfl)
  have compositeThenTensor :
      CategoryHomCarrier (append a0 c0) (append a2 c2)
        (append (append f fPrime) (append g gPrime)) :=
    (MonoidalCatSingleton_tensor_carrier fThenFPrime gThenGPrime).right
  have displayedSame :
      hsame (append (append f g) (append fPrime gPrime))
        (append (append f fPrime) (append g gPrime)) := by
    calc
      append (append f g) (append fPrime gPrime)
          = append f (append g (append fPrime gPrime)) :=
            append_assoc f g (append fPrime gPrime)
      _ = append f (append (append g fPrime) gPrime) :=
            congrArg (append f) (append_assoc g fPrime gPrime).symm
      _ = append f (append (append fPrime g) gPrime) :=
            congrArg (fun x => append f (append x gPrime))
              (unary_append_comm gCarrier.right.right.left fPrimeCarrier.right.right.left)
      _ = append f (append fPrime (append g gPrime)) :=
            congrArg (append f) (append_assoc fPrime g gPrime)
      _ = append (append f fPrime) (append g gPrime) :=
            (append_assoc f fPrime (append g gPrime)).symm
  exact And.intro tensorThenComposite
    (And.intro compositeThenTensor displayedSame)

theorem MonoidalCatSingleton_coherence_laws
    {w x y z pentagonLeft pentagonRight triangleLeft triangleRight : BHist} :
    UnaryHistory w ->
      UnaryHistory x ->
        UnaryHistory y ->
          UnaryHistory z ->
            Cont (append (append (append w x) y) z) BHist.Empty pentagonLeft ->
              Cont (append w (append x (append y z))) BHist.Empty pentagonRight ->
                Cont (append (append x BHist.Empty) y) BHist.Empty triangleLeft ->
                  Cont (append x y) BHist.Empty triangleRight ->
                    hsame pentagonLeft pentagonRight ∧ hsame triangleLeft triangleRight ∧
                      UnaryHistory pentagonLeft ∧ UnaryHistory pentagonRight := by
  intro wUnary xUnary yUnary zUnary pentagonLeftCont pentagonRightCont triangleLeftCont
    triangleRightCont
  have pentagonLeftUnary :
      UnaryHistory (append (append (append w x) y) z) :=
    unary_append_closed (unary_append_closed (unary_append_closed wUnary xUnary) yUnary)
      zUnary
  have pentagonRightUnary :
      UnaryHistory (append w (append x (append y z))) :=
    unary_append_closed wUnary
      (unary_append_closed xUnary (unary_append_closed yUnary zUnary))
  have pentagonLeftSame :
      hsame pentagonLeft (append (append (append w x) y) z) :=
    cont_right_unit_iff.mp pentagonLeftCont
  have pentagonRightSame :
      hsame pentagonRight (append w (append x (append y z))) :=
    cont_right_unit_iff.mp pentagonRightCont
  have pentagonSpine :
      hsame (append (append (append w x) y) z)
        (append w (append x (append y z))) :=
    hsame_trans (append_assoc (append w x) y z)
      (append_assoc w x (append y z))
  have pentagonSame : hsame pentagonLeft pentagonRight :=
    hsame_trans pentagonLeftSame
      (hsame_trans pentagonSpine (hsame_symm pentagonRightSame))
  have triangleLeftSame :
      hsame triangleLeft (append (append x BHist.Empty) y) :=
    cont_right_unit_iff.mp triangleLeftCont
  have triangleRightSame : hsame triangleRight (append x y) :=
    cont_right_unit_iff.mp triangleRightCont
  have triangleSpine :
      hsame (append (append x BHist.Empty) y) (append x y) :=
    congrArg (fun h => append h y) (append_empty_right x)
  have triangleSame : hsame triangleLeft triangleRight :=
    hsame_trans triangleLeftSame
      (hsame_trans triangleSpine (hsame_symm triangleRightSame))
  have pentagonLeftCarrier : UnaryHistory pentagonLeft :=
    unary_transport pentagonLeftUnary (hsame_symm pentagonLeftSame)
  have pentagonRightCarrier : UnaryHistory pentagonRight :=
    unary_transport pentagonRightUnary (hsame_symm pentagonRightSame)
  exact And.intro pentagonSame
    (And.intro triangleSame (And.intro pentagonLeftCarrier pentagonRightCarrier))

end BEDC.Derived.MonoidalCatUp
