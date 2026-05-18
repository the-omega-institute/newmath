import BEDC.Derived.CategoryUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.UnaryContinuationEndofunctorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

def UnaryContinuationEndofunctorCarrier
    (object hom action identity composition transport route provenance localName : BHist) :
    Prop :=
  UnaryHistory object ∧ UnaryHistory hom ∧ UnaryHistory action ∧ UnaryHistory identity ∧
    UnaryHistory composition ∧
      Cont object action transport ∧
        Cont hom identity route ∧
          Cont composition transport provenance ∧ hsame provenance localName

theorem UnaryContinuationEndofunctorCarrier_composition_stability
    {object hom action identity composition transport route provenance localName source mid target f g
      fg imageF imageG imageFG imageComp : BHist} :
    UnaryContinuationEndofunctorCarrier object hom action identity composition transport route
      provenance localName ->
      CategoryHomCarrier source mid f ->
        CategoryHomCarrier mid target g ->
          Cont f g fg ->
            Cont action f imageF ->
              Cont action g imageG ->
                Cont action fg imageFG ->
                  Cont imageF imageG imageComp ->
                    hsame imageFG imageComp ->
                      CategoryHomCarrier source target fg ∧ UnaryHistory imageFG ∧
                        UnaryHistory imageComp ∧ hsame imageFG imageComp := by
  -- BEDC touchpoint anchor: BHist Cont hsame CategoryHomCarrier UnaryHistory
  intro _carrier left right comp actionF actionG actionFG imageCompRel sameImage
  have composite : CategoryHomCarrier source target fg :=
    CategoryHomCarrier_comp_closed left right comp
  have actionUnary : UnaryHistory action := _carrier.right.right.left
  have imageFGUnary : UnaryHistory imageFG :=
    unary_cont_closed actionUnary composite.right.right.left actionFG
  have imageFUnary : UnaryHistory imageF :=
    unary_cont_closed actionUnary left.right.right.left actionF
  have imageGUnary : UnaryHistory imageG :=
    unary_cont_closed actionUnary right.right.right.left actionG
  have imageCompUnary : UnaryHistory imageComp :=
    unary_cont_closed imageFUnary imageGUnary imageCompRel
  exact And.intro composite
    (And.intro imageFGUnary (And.intro imageCompUnary sameImage))

end BEDC.Derived.UnaryContinuationEndofunctorUp
