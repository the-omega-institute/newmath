import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_semanticNameCert_of_hom {a b f : BHist} :
    CategoryHomCarrier a b f ->
      BEDC.FKernel.NameCert.SemanticNameCert (CategoryHomCarrier a b)
        (CategoryHomCarrier a b) (CategoryHomCarrier a b) hsame := by
  intro homCarrier
  constructor
  · constructor
    · exact Exists.intro f homCarrier
    · intro h _homCarrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrierH
      exact CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl b) same carrierH
  · intro h source
    exact source
  · intro h source
    exact source

theorem CategoryHomCarrier_empty_source_semanticNameCert {b : BHist}
    (targetCarrier : UnaryHistory b) :
    SemanticNameCert (CategoryHomCarrier BHist.Empty b) (CategoryHomCarrier BHist.Empty b)
      (CategoryHomCarrier BHist.Empty b) hsame := by
  constructor
  · constructor
    · exact Exists.intro b
        ((CategoryHomCarrier_empty_source_iff (b := b) (f := b)).mpr
          (And.intro targetCarrier (hsame_refl b)))
    · intro h _homCarrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same homCarrier
      exact CategoryHomCarrier_hsame_transport (hsame_refl BHist.Empty) (hsame_refl b) same
        homCarrier
  · intro h source
    exact source
  · intro h source
    exact source

theorem CategoryHomCarrier_empty_target_semanticNameCert {a : BHist}
    (sourceEmpty : hsame a BHist.Empty) :
    SemanticNameCert (CategoryHomCarrier a BHist.Empty) (CategoryHomCarrier a BHist.Empty)
      (CategoryHomCarrier a BHist.Empty) hsame := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty
        ((CategoryHomCarrier_empty_target_iff (a := a) (f := BHist.Empty)).mpr
          (And.intro sourceEmpty (hsame_refl BHist.Empty)))
    · intro h _homCarrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same homCarrier
      exact CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl BHist.Empty) same
        homCarrier
  · intro h source
    exact source
  · intro h source
    exact source

theorem CategoryHomCarrier_comp_result_semanticNameCert {a b c f g fg : BHist}
    (left : CategoryHomCarrier a b f) (right : CategoryHomCarrier b c g) (comp : Cont f g fg) :
    SemanticNameCert (fun h : BHist => CategoryHomCarrier a c h ∧ hsame h fg)
      (fun h : BHist => CategoryHomCarrier a c h ∧ hsame h fg)
      (fun h : BHist => CategoryHomCarrier a c h ∧ hsame h fg) hsame := by
  constructor
  · constructor
    · exact Exists.intro fg
        (And.intro (CategoryHomCarrier_comp_closed left right comp) (hsame_refl fg))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro
        (CategoryHomCarrier_hsame_transport (hsame_refl a) (hsame_refl c) same carrier.left)
        (hsame_trans (hsame_symm same) carrier.right)
  · intro h source
    exact source
  · intro h source
    exact source

theorem CategoryHomCarrier_comp_result_endpoint_semanticNameCert {a b c a' c' f g fg : BHist}
    (sameSource : hsame a a') (sameTarget : hsame c c')
    (left : CategoryHomCarrier a b f) (right : CategoryHomCarrier b c g) (comp : Cont f g fg) :
    SemanticNameCert (fun h : BHist => CategoryHomCarrier a' c' h ∧ hsame h fg)
      (fun h : BHist => CategoryHomCarrier a' c' h ∧ hsame h fg)
      (fun h : BHist => CategoryHomCarrier a' c' h ∧ hsame h fg) hsame := by
  constructor
  · constructor
    · have composite : CategoryHomCarrier a c fg :=
        CategoryHomCarrier_comp_closed left right comp
      exact Exists.intro fg
        (And.intro
          (CategoryHomCarrier_hsame_transport sameSource sameTarget (hsame_refl fg) composite)
          (hsame_refl fg))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact And.intro
        (CategoryHomCarrier_hsame_transport (hsame_refl a') (hsame_refl c') same carrier.left)
        (hsame_trans (hsame_symm same) carrier.right)
  · intro h source
    exact source
  · intro h source
    exact source

theorem CategoryHomCarrier_unary_suffix_semantic_boundary {q a b f : BHist} :
    UnaryHistory q -> CategoryHomCarrier a b f ->
      SemanticNameCert (CategoryHomCarrier (append a q) (append b q))
        (CategoryHomCarrier (append a q) (append b q))
        (CategoryHomCarrier (append a q) (append b q)) hsame ∧
        (CategoryHomCarrier (append a q) (append b q) f ↔
          UnaryHistory q ∧ CategoryHomCarrier a b f) := by
  intro suffixCarrier homCarrier
  have suffixedHom : CategoryHomCarrier (append a q) (append b q) f :=
    CategoryHomCarrier_unary_suffix_iff.mpr (And.intro suffixCarrier homCarrier)
  exact And.intro (CategoryHomCarrier_semanticNameCert_of_hom suffixedHom)
    CategoryHomCarrier_unary_suffix_iff

end BEDC.Derived.CategoryUp
