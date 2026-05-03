import BEDC.Derived.FunctorUp
import BEDC.FKernel.NameCert
import BEDC.Derived.ContinuousMapUp
import BEDC.Derived.LinearMapUp

namespace BEDC.Derived.FuncobjUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp
open BEDC.Derived.FunctorUp
open BEDC.Derived.ContinuousMapUp
open BEDC.Derived.LinearMapUp

theorem FuncobjPointwiseHomCarrier_semanticNameCert {p a b f : BHist}
    (prefixCarrier : UnaryHistory p) (hom : CategoryHomCarrier a b f) :
    SemanticNameCert
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier (append p a) (append p b) t)
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier (append p a) (append p b) t)
      (fun t : BHist =>
        CategoryHomCarrier a b t ∧ CategoryHomCarrier (append p a) (append p b) t)
      hsame := by
  constructor
  · constructor
    · exact Exists.intro f
        (And.intro hom (FunctorPrefixHomCarrier_preserves prefixCarrier hom))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro
        (CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) same carrier.left)
        (CategoryHomCarrier_hsame_transport (hsame_refl (append p a))
          (hsame_refl (append p b)) same carrier.right)
  · intro h source
    exact source
  · intro h source
    exact source

theorem FuncObjLinearSingleton_continuous_map_components_empty
    {source map target modulus cert distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      LinearMapSingletonCarrier source -> LinearMapSingletonCarrier map ->
        LinearMapSingletonCarrier modulus ->
          hsame target BHist.Empty ∧ hsame cert BHist.Empty ∧
            hsame distance BHist.Empty := by
  intro carrier sourceEmpty mapEmpty modulusEmpty
  have graphRel : Cont source map target :=
    carrier.left.right.right.right.right.left
  have certRel : Cont target modulus cert :=
    carrier.left.right.right.right.right.right
  have distanceRel : Cont source target distance :=
    carrier.right.right.right.right
  have targetEmpty : hsame target BHist.Empty :=
    cont_respects_hsame sourceEmpty mapEmpty graphRel (cont_right_unit BHist.Empty)
  have certEmpty : hsame cert BHist.Empty :=
    cont_respects_hsame targetEmpty modulusEmpty certRel (cont_right_unit BHist.Empty)
  have distanceEmpty : hsame distance BHist.Empty :=
    cont_respects_hsame sourceEmpty targetEmpty distanceRel (cont_right_unit BHist.Empty)
  exact And.intro targetEmpty (And.intro certEmpty distanceEmpty)

end BEDC.Derived.FuncobjUp
