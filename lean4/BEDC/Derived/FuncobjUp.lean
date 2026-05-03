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

theorem FuncobjPointwiseHomCarrier_comp_public_readback {p a b c f g fg : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      (CategoryHomCarrier a c fg ∧ CategoryHomCarrier (append p a) (append p c) fg) ∧
        (forall {displayed : BHist},
          CategoryHomCarrier a c displayed ∧
            CategoryHomCarrier (append p a) (append p c) displayed ->
              hsame fg displayed) := by
  intro prefixCarrier left right comp
  have baseReadback := CategoryHomCarrier_comp_public_readback left right comp
  have prefixedCarrier : CategoryHomCarrier (append p a) (append p c) fg :=
    FunctorPrefixHomCarrier_preserves prefixCarrier baseReadback.left
  constructor
  · exact And.intro baseReadback.left prefixedCarrier
  · intro displayed displayedCarrier
    exact baseReadback.right displayedCarrier.left

theorem FuncobjPointwiseHomCarrier_comp_hsame_transport {p a b c f g fg fg' : BHist} :
    UnaryHistory p -> CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g fg ->
      hsame fg fg' ->
        CategoryHomCarrier a c fg' ∧ CategoryHomCarrier (append p a) (append p c) fg' := by
  intro prefixCarrier left right comp sameComposite
  have carriers :=
    (FuncobjPointwiseHomCarrier_comp_public_readback prefixCarrier left right comp).left
  exact And.intro
    (CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl c) sameComposite
      carriers.left)
    (CategoryHomCarrier_hsame_transport (hsame_refl (append p a)) (hsame_refl (append p c))
      sameComposite carriers.right)

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

theorem FuncObjLinearSingleton_continuous_map_empty_graphs
    {source map target modulus cert distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      LinearMapSingletonCarrier source -> LinearMapSingletonCarrier map ->
        LinearMapSingletonCarrier modulus ->
          Cont source map BHist.Empty ∧ Cont BHist.Empty modulus cert ∧
            Cont source BHist.Empty distance := by
  intro carrier sourceEmpty mapEmpty modulusEmpty
  have emptyComponents :=
    FuncObjLinearSingleton_continuous_map_components_empty
      carrier sourceEmpty mapEmpty modulusEmpty
  have graphRel : Cont source map target :=
    carrier.left.right.right.right.right.left
  have certRel : Cont target modulus cert :=
    carrier.left.right.right.right.right.right
  have distanceRel : Cont source target distance :=
    carrier.right.right.right.right
  exact And.intro
    (cont_result_hsame_transport graphRel emptyComponents.left)
    (And.intro
      (cont_hsame_transport emptyComponents.left (hsame_refl modulus) (hsame_refl cert) certRel)
      (cont_hsame_transport (hsame_refl source) emptyComponents.left (hsame_refl distance)
        distanceRel))

theorem FuncObjLinearSingleton_continuous_map_empty_components_iff
    {source map target modulus cert distance : BHist} :
    LinearMapSingletonCarrier source -> LinearMapSingletonCarrier map ->
      LinearMapSingletonCarrier modulus ->
        (ContinuousMapCarrier source map target modulus cert distance ↔
          hsame target BHist.Empty ∧ hsame cert BHist.Empty ∧
            hsame distance BHist.Empty) := by
  intro sourceEmpty mapEmpty modulusEmpty
  constructor
  · intro carrier
    exact
      FuncObjLinearSingleton_continuous_map_components_empty
        carrier sourceEmpty mapEmpty modulusEmpty
  · intro componentsEmpty
    cases sourceEmpty
    cases mapEmpty
    cases modulusEmpty
    cases componentsEmpty.left
    cases componentsEmpty.right.left
    cases componentsEmpty.right.right
    exact
      And.intro
        (And.intro unary_empty
          (And.intro unary_empty
            (And.intro unary_empty
              (And.intro unary_empty
                (And.intro (cont_right_unit BHist.Empty) (cont_right_unit BHist.Empty))))))
        (And.intro unary_empty
          (And.intro unary_empty
            (And.intro unary_empty (cont_right_unit BHist.Empty))))

theorem FuncObjLinearSingleton_continuous_map_target_graph_empty_iff
    {source map target modulus cert distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      LinearMapSingletonCarrier source -> LinearMapSingletonCarrier map ->
        (Cont source map BHist.Empty ↔ hsame target BHist.Empty) := by
  intro carrier sourceEmpty mapEmpty
  have graphRel : Cont source map target :=
    carrier.left.right.right.right.right.left
  constructor
  · intro _emptyGraph
    exact cont_respects_hsame sourceEmpty mapEmpty graphRel (cont_right_unit BHist.Empty)
  · intro targetEmpty
    exact cont_result_hsame_transport graphRel targetEmpty

theorem FuncObjLinearSingleton_continuous_map_cert_graph_empty_iff
    {source map target modulus cert distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      LinearMapSingletonCarrier target -> LinearMapSingletonCarrier modulus ->
        (Cont target modulus BHist.Empty ↔ hsame cert BHist.Empty) := by
  intro carrier _targetEmpty _modulusEmpty
  have certRel : Cont target modulus cert :=
    carrier.left.right.right.right.right.right
  constructor
  · intro emptyCertGraph
    exact cont_deterministic certRel emptyCertGraph
  · intro certEmpty
    exact cont_result_hsame_transport certRel certEmpty

theorem FuncObjLinearSingleton_continuous_map_distance_graph_empty_iff
    {source map target modulus cert distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      (Cont source target BHist.Empty ↔ hsame distance BHist.Empty) := by
  intro carrier
  have distanceRel : Cont source target distance :=
    carrier.right.right.right.right
  constructor
  · intro emptyDistanceGraph
    exact cont_deterministic distanceRel emptyDistanceGraph
  · intro distanceEmpty
    exact cont_result_hsame_transport distanceRel distanceEmpty

end BEDC.Derived.FuncobjUp
