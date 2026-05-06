import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.EqtypeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def EqtypeClassCarrier (anchor : BHist) (h : BHist) : Prop :=
  hsame h anchor

theorem EqtypeClassCarrier_e1_anchor_tail_readback {anchor tail h : BHist} :
    EqtypeClassCarrier (BHist.e1 anchor) h -> hsame h (BHist.e1 tail) ->
      hsame tail anchor := by
  intro carrier sameTail
  have sameAnchored : hsame (BHist.e1 tail) (BHist.e1 anchor) :=
    hsame_trans (hsame_symm sameTail) carrier
  exact hsame_e1_iff.mp sameAnchored

theorem EqtypeClassCarrier_e0_anchor_tail_readback {anchor tail h : BHist} :
    EqtypeClassCarrier (BHist.e0 anchor) h -> hsame h (BHist.e0 tail) ->
      hsame tail anchor := by
  intro carrier sameTail
  have sameAnchored : hsame (BHist.e0 tail) (BHist.e0 anchor) :=
    hsame_trans (hsame_symm sameTail) carrier
  exact hsame_e0_iff.mp sameAnchored

theorem EqtypeClassCarrier_e0_anchor_pair_deterministic {anchor left right : BHist} :
    EqtypeClassCarrier (BHist.e0 anchor) left ->
      EqtypeClassCarrier (BHist.e0 anchor) right -> hsame left right := by
  intro leftCarrier rightCarrier
  exact hsame_trans leftCarrier (hsame_symm rightCarrier)

theorem EqtypeClassCarrier_e0_anchor_e1_tail_absurd {anchor tail h : BHist} :
    EqtypeClassCarrier (BHist.e0 anchor) h -> hsame h (BHist.e1 tail) -> False := by
  intro carrier sameTail
  have mixed : hsame (BHist.e1 tail) (BHist.e0 anchor) :=
    hsame_trans (hsame_symm sameTail) carrier
  exact not_hsame_e1_e0 mixed

theorem EqtypeClassCarrier_e1_anchor_e0_tail_absurd {anchor tail h : BHist} :
    EqtypeClassCarrier (BHist.e1 anchor) h -> hsame h (BHist.e0 tail) -> False := by
  intro carrier sameTail
  have mixed : hsame (BHist.e0 tail) (BHist.e1 anchor) :=
    hsame_trans (hsame_symm sameTail) carrier
  exact not_hsame_e0_e1 mixed

theorem EqtypeClassCarrier_empty_anchor_visible_absurd {tail h : BHist} :
    EqtypeClassCarrier BHist.Empty h ->
      (hsame h (BHist.e0 tail) ∨ hsame h (BHist.e1 tail)) -> False := by
  intro carrier visible
  cases visible with
  | inl sameZero =>
      exact not_hsame_emp_e0 (hsame_trans (hsame_symm carrier) sameZero)
  | inr sameOne =>
      exact not_hsame_emp_e1 (hsame_trans (hsame_symm carrier) sameOne)

theorem EqtypeClassCarrier_visible_context_anchor_readback {p r anchor h core : BHist} :
    EqtypeClassCarrier anchor h ->
      hsame (append (append p h) r) (append (append p core) r) ->
        hsame core anchor := by
  intro carrier sameVisible
  have sameNested : hsame (append p (append h r)) (append p (append core r)) :=
    hsame_trans (hsame_symm (append_assoc p h r))
      (hsame_trans sameVisible (append_assoc p core r))
  have sameCore : hsame h core :=
    (append_hsame_common_context_cancel_iff (hsame_refl p) (hsame_refl r)).mp sameNested
  exact hsame_trans (hsame_symm sameCore) carrier

theorem EqtypeClassCarrier_visible_context_empty_anchor_visible_core_absurd
    {p r h core tail : BHist} :
    EqtypeClassCarrier BHist.Empty h ->
      hsame (append (append p h) r) (append (append p core) r) ->
        (hsame core (BHist.e0 tail) ∨ hsame core (BHist.e1 tail)) -> False := by
  intro carrier sameVisible visibleCore
  have coreCarrier : EqtypeClassCarrier BHist.Empty core :=
    EqtypeClassCarrier_visible_context_anchor_readback carrier sameVisible
  exact EqtypeClassCarrier_empty_anchor_visible_absurd coreCarrier visibleCore

theorem EqtypeClassCarrier_visible_context_cores_deterministic
    {p r anchor left right coreLeft coreRight : BHist} :
    EqtypeClassCarrier anchor left -> EqtypeClassCarrier anchor right ->
      hsame (append (append p left) r) (append (append p coreLeft) r) ->
        hsame (append (append p right) r) (append (append p coreRight) r) ->
          hsame coreLeft coreRight := by
  intro leftCarrier rightCarrier leftVisible rightVisible
  have leftReadback : hsame coreLeft anchor :=
    EqtypeClassCarrier_visible_context_anchor_readback leftCarrier leftVisible
  have rightReadback : hsame coreRight anchor :=
    EqtypeClassCarrier_visible_context_anchor_readback rightCarrier rightVisible
  exact hsame_trans leftReadback (hsame_symm rightReadback)

theorem EqtypeClassCarrier_visible_context_pair_deterministic
    {p r anchor left right leftCore rightCore : BHist} :
    EqtypeClassCarrier anchor left -> EqtypeClassCarrier anchor right ->
      hsame (append (append p left) r) (append (append p leftCore) r) ->
        hsame (append (append p right) r) (append (append p rightCore) r) ->
          hsame leftCore rightCore := by
  intro leftCarrier rightCarrier sameLeft sameRight
  have leftCoreAnchor : hsame leftCore anchor :=
    EqtypeClassCarrier_visible_context_anchor_readback leftCarrier sameLeft
  have rightCoreAnchor : hsame rightCore anchor :=
    EqtypeClassCarrier_visible_context_anchor_readback rightCarrier sameRight
  exact hsame_trans leftCoreAnchor (hsame_symm rightCoreAnchor)

theorem EqtypeClassCarrier_visible_context_e0_anchor_e1_tail_absurd
    {p r anchor h tail : BHist} :
    EqtypeClassCarrier (BHist.e0 anchor) h ->
      hsame (append (append p h) r) (append (append p (BHist.e1 tail)) r) -> False := by
  intro carrier sameVisible
  have mixed : hsame (BHist.e1 tail) (BHist.e0 anchor) :=
    EqtypeClassCarrier_visible_context_anchor_readback carrier sameVisible
  exact not_hsame_e1_e0 mixed

theorem EqtypeClassCarrier_anchor_hsame_transport {anchor anchor' h : BHist} :
    EqtypeClassCarrier anchor h -> hsame anchor anchor' ->
      EqtypeClassCarrier anchor' h ∧ hsame (append h BHist.Empty) anchor' := by
  intro carrier sameAnchor
  have transported : EqtypeClassCarrier anchor' h :=
    hsame_trans carrier sameAnchor
  have endpoint : hsame (append h BHist.Empty) anchor' :=
    hsame_trans (append_empty_right h) transported
  exact ⟨transported, endpoint⟩

theorem EqtypeClassCarrier_transitive {anchor h h' : BHist} :
    EqtypeClassCarrier anchor h -> EqtypeClassCarrier h h' ->
      EqtypeClassCarrier anchor h' ∧ hsame (append h' BHist.Empty) anchor := by
  intro carrier step
  have transported : EqtypeClassCarrier anchor h' :=
    hsame_trans step carrier
  have endpoint : hsame (append h' BHist.Empty) anchor :=
    hsame_trans (append_empty_right h') transported
  exact ⟨transported, endpoint⟩

theorem EqtypeClass_semanticNameCert {anchor : BHist} :
    SemanticNameCert (EqtypeClassCarrier anchor) (EqtypeClassCarrier anchor)
      (EqtypeClassCarrier anchor) hsame := by
  constructor
  · constructor
    · exact Exists.intro anchor (hsame_refl anchor)
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      exact hsame_trans (hsame_symm same) carrier
  · intro h source
    exact source
  · intro h source
    exact source

theorem EqtypeIdentity_semanticNameCert :
    SemanticNameCert (fun h : BHist => hsame h h)
      (fun h : BHist => hsame h h)
      (fun h : BHist => hsame h h)
      hsame := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty (hsame_refl BHist.Empty)
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro _h _k same
        exact hsame_symm same
      equiv_trans := by
        intro _h _k _r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro _h k _same _carrier
        exact hsame_refl k
    }
    pattern_sound := by
      intro _h carrier
      exact carrier
    ledger_sound := by
      intro _h carrier
      exact carrier
  }

end BEDC.Derived.EqtypeUp
