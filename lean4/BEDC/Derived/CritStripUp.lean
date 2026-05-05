import BEDC.FKernel.NameCert
import BEDC.Derived.NatUp
import BEDC.Derived.RatUp

namespace BEDC.Derived.CritStripUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.RatUp

def CritStripOpenInterval (sigma : BHist) : Prop :=
  NatUnaryStrictPrefix BHist.Empty sigma ∧
    NatUnaryStrictPrefix sigma (BHist.e1 BHist.Empty)

theorem CritStripOpenInterval_unary_boundary_exclusion {sigma : BHist} :
    CritStripOpenInterval sigma ->
      UnaryHistory sigma ∧ (hsame sigma BHist.Empty -> False) ∧
        (hsame sigma (BHist.e1 BHist.Empty) -> False) := by
  intro strip
  have sigmaUnary : UnaryHistory sigma := by
    cases strip.left with
    | intro tail data =>
        have sameSigmaTail : hsame sigma tail := cont_left_unit_result data.right.right
        exact unary_transport data.left (hsame_symm sameSigmaTail)
  constructor
  · exact sigmaUnary
  · constructor
    · intro sameEmpty
      cases sameEmpty
      exact NatUnaryStrictPrefix_empty_right_absurd strip.left
    · intro sameOne
      cases sameOne
      exact NatUnaryStrictPrefix_asymm strip.right strip.right

theorem CritStripOpenInterval_empty_unit_absurd {sigma : BHist} :
    NatUnaryStrictPrefix BHist.Empty sigma ->
      NatUnaryStrictPrefix sigma (BHist.e1 BHist.Empty) -> False := by
  intro lower upper
  have sigmaUnary : UnaryHistory sigma :=
    NatUnaryStrictPrefix_target_unary unary_empty lower
  cases unary_history_cases sigmaUnary with
  | inl sigmaEmpty =>
      cases sigmaEmpty
      exact NatUnaryStrictPrefix_empty_right_absurd lower
  | inr sigmaStep =>
      cases sigmaStep with
      | intro tail tailData =>
          cases tailData with
          | intro sigmaEq _tailUnary =>
              cases sigmaEq
              exact NatUnaryStrictPrefix_empty_right_absurd
                (NatUnaryStrictPrefix_e1_inversion upper)

def InCritStrip (sigma : BHist) : Prop :=
  NatUnaryStrictPrefix BHist.Empty sigma ∧
    NatUnaryStrictPrefix sigma (BHist.e1 BHist.Empty)

def CritStripSourceSpec (h : BHist) : Prop :=
  hsame h BHist.Empty ∧ (InCritStrip h -> False)

def CompactSubStrip (epsilon T s : BHist) : Prop :=
  InCritStrip s ∧ UnaryHistory epsilon ∧ UnaryHistory T

theorem CompactSubStrip_empty_unit_obstruction_decidable (epsilon T s : BHist) :
    CompactSubStrip epsilon T s -> False := by
  intro compact
  exact CritStripOpenInterval_empty_unit_absurd compact.left.left compact.left.right

def InCritStrip_open_interval_decidable (sigma : BHist) :
    Decidable
      (NatUnaryStrictPrefix BHist.Empty sigma ∧
        NatUnaryStrictPrefix sigma (BHist.e1 BHist.Empty)) := by
  exact Decidable.isFalse
    (fun strip => CritStripOpenInterval_empty_unit_absurd strip.left strip.right)

def OnCritLine (sigma : BHist) : Prop :=
  hsame sigma (BHist.e1 (BHist.e1 BHist.Empty))

def OnCritLine_decidable (sigma : BHist) : Decidable (OnCritLine sigma) := by
  unfold OnCritLine hsame
  exact inferInstance

theorem InCritStrip_boundary_excluded {sigma : BHist} :
    InCritStrip sigma ->
      (hsame sigma BHist.Empty -> False) ∧
        (hsame sigma (BHist.e1 BHist.Empty) -> False) := by
  intro strip
  constructor
  · intro sameEmpty
    cases sameEmpty
    exact NatUnaryStrictPrefix_asymm strip.left strip.left
  · intro sameUnit
    cases sameUnit
    exact NatUnaryStrictPrefix_asymm strip.right strip.right

theorem CritStripSourceSpec_empty_boundary : CritStripSourceSpec BHist.Empty := by
  exact And.intro (hsame_refl BHist.Empty)
    (fun strip => (InCritStrip_boundary_excluded strip).left (hsame_refl BHist.Empty))

theorem InCritStrip_hsame_transport_boundary_exclusion {sigma sigma' : BHist} :
    InCritStrip sigma -> hsame sigma sigma' ->
      InCritStrip sigma' ∧ (hsame sigma' BHist.Empty -> False) ∧
        (hsame sigma' (BHist.e1 BHist.Empty) -> False) := by
  intro strip sameSigma
  have leftStrict : NatUnaryStrictPrefix BHist.Empty sigma' := by
    cases strip.left with
    | intro tail data =>
        exact NatUnaryStrictPrefix_cont_hsame_transport data.left data.right.left
          data.right.right (hsame_refl BHist.Empty) sameSigma
  have rightStrict : NatUnaryStrictPrefix sigma' (BHist.e1 BHist.Empty) := by
    cases strip.right with
    | intro tail data =>
        exact NatUnaryStrictPrefix_cont_hsame_transport data.left data.right.left
          data.right.right sameSigma (hsame_refl (BHist.e1 BHist.Empty))
  have transported : InCritStrip sigma' := And.intro leftStrict rightStrict
  exact And.intro transported (InCritStrip_boundary_excluded transported)

def CritStripComplexCarrier (s sigma tau : BHist) : Prop :=
  RatHistoryCarrier sigma ∧ RatHistoryCarrier tau ∧ Cont sigma tau s ∧ InCritStrip sigma

def CritStripClassifierSpec (s t sigma sigma' tau tau' : BHist) : Prop :=
  CritStripComplexCarrier s sigma tau ∧ CritStripComplexCarrier t sigma' tau' ∧
    hsame sigma sigma' ∧ hsame tau tau'

theorem CritStripComplexCarrier_not_empty {s sigma tau : BHist} :
    CritStripComplexCarrier s sigma tau -> hsame s BHist.Empty -> False := by
  intro carrier sameEmpty
  have emptyCont : Cont sigma tau BHist.Empty :=
    cont_result_hsame_transport carrier.right.right.left sameEmpty
  have endpoints : sigma = BHist.Empty ∧ tau = BHist.Empty :=
    cont_empty_result_inversion emptyCont
  exact RatHistoryCarrier_not_empty carrier.left endpoints.left

theorem CritStripComplexCarrier_strict_interval_absurd {s sigma tau : BHist} :
    CritStripComplexCarrier s sigma tau ->
      (NatUnaryStrictPrefix BHist.Empty sigma ∧
        NatUnaryStrictPrefix sigma (BHist.e1 BHist.Empty)) ∧ False := by
  intro carrier
  have interval : NatUnaryStrictPrefix BHist.Empty sigma ∧
      NatUnaryStrictPrefix sigma (BHist.e1 BHist.Empty) :=
    And.intro carrier.right.right.right.left carrier.right.right.right.right
  exact And.intro interval
    (CritStripOpenInterval_empty_unit_absurd interval.left interval.right)

theorem CritStripComplexCarrier_hsame_transport {s s' sigma sigma' tau tau' : BHist} :
    hsame s s' -> hsame sigma sigma' -> hsame tau tau' ->
      CritStripComplexCarrier s sigma tau ->
        CritStripComplexCarrier s' sigma' tau' ∧ Cont sigma' tau' s' ∧ False := by
  intro sameS sameSigma sameTau carrier
  have sigmaCarrier : RatHistoryCarrier sigma' :=
    RatHistoryCarrier_hsame_transport sameSigma carrier.left
  have tauCarrier : RatHistoryCarrier tau' :=
    RatHistoryCarrier_hsame_transport sameTau carrier.right.left
  have transportedStrip :=
    InCritStrip_hsame_transport_boundary_exclusion carrier.right.right.right sameSigma
  have transportedCont : Cont sigma' tau' s' := by
    cases sameS
    cases sameSigma
    cases sameTau
    exact carrier.right.right.left
  have transportedCarrier : CritStripComplexCarrier s' sigma' tau' :=
    And.intro sigmaCarrier
      (And.intro tauCarrier (And.intro transportedCont transportedStrip.left))
  exact And.intro transportedCarrier
    (And.intro transportedCont
      (CritStripComplexCarrier_strict_interval_absurd transportedCarrier).right)

theorem CritStripStabilityCert_fields :
    (forall {sigma sigma' : BHist}, InCritStrip sigma -> hsame sigma sigma' ->
      InCritStrip sigma' ∧ (hsame sigma' BHist.Empty -> False) ∧
        (hsame sigma' (BHist.e1 BHist.Empty) -> False)) ∧
      (forall {s s' sigma sigma' tau tau' : BHist}, hsame s s' -> hsame sigma sigma' ->
        hsame tau tau' -> CritStripComplexCarrier s sigma tau ->
          CritStripComplexCarrier s' sigma' tau' ∧ Cont sigma' tau' s' ∧ False) := by
  constructor
  · intro sigma sigma' strip sameSigma
    exact InCritStrip_hsame_transport_boundary_exclusion strip sameSigma
  · intro s s' sigma sigma' tau tau' sameS sameSigma sameTau carrier
    exact CritStripComplexCarrier_hsame_transport sameS sameSigma sameTau carrier

theorem CritStripComplexCarrier_component_boundary_exclusion {s sigma tau : BHist} :
    CritStripComplexCarrier s sigma tau ->
      (hsame sigma BHist.Empty -> False) ∧
        (hsame sigma (BHist.e1 BHist.Empty) -> False) ∧
          (hsame tau BHist.Empty -> False) ∧ (hsame s BHist.Empty -> False) := by
  intro carrier
  have sigmaExcluded := InCritStrip_boundary_excluded carrier.right.right.right
  exact And.intro sigmaExcluded.left
    (And.intro sigmaExcluded.right
      (And.intro
        (RatHistoryCarrier_not_empty carrier.right.left)
        (CritStripComplexCarrier_not_empty carrier)))

theorem CritStripClassifierSpec_component_transport
    {s t sigma sigma' tau tau' u v rho rho' ups ups' : BHist} :
    hsame s u -> hsame t v -> hsame sigma rho -> hsame sigma' rho' ->
      hsame tau ups -> hsame tau' ups' ->
        CritStripClassifierSpec s t sigma sigma' tau tau' ->
          CritStripClassifierSpec u v rho rho' ups ups' ∧ Cont rho ups u ∧
            Cont rho' ups' v := by
  intro sameS sameT sameSigma sameSigma' sameTau sameTau' classified
  cases classified with
  | intro leftCarrier rest =>
      cases rest with
      | intro rightCarrier sameComponents =>
          have transportedLeft :=
            CritStripComplexCarrier_hsame_transport sameS sameSigma sameTau leftCarrier
          have transportedRight :=
            CritStripComplexCarrier_hsame_transport sameT sameSigma' sameTau' rightCarrier
          have sameRhoRho' : hsame rho rho' :=
            hsame_trans (hsame_symm sameSigma)
              (hsame_trans sameComponents.left sameSigma')
          have sameUpsUps' : hsame ups ups' :=
            hsame_trans (hsame_symm sameTau)
              (hsame_trans sameComponents.right sameTau')
          exact And.intro
            (And.intro transportedLeft.left
              (And.intro transportedRight.left
                (And.intro sameRhoRho' sameUpsUps')))
            (And.intro transportedLeft.right.left transportedRight.right.left)

theorem CritStripEmptyBoundary_semanticNameCert :
    SemanticNameCert
      (fun h : BHist => hsame h BHist.Empty ∧ (InCritStrip h -> False))
      (fun h : BHist => hsame h BHist.Empty ∧ (InCritStrip h -> False))
      (fun h : BHist => hsame h BHist.Empty ∧ (InCritStrip h -> False))
      hsame := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty
        (And.intro (hsame_refl BHist.Empty)
          (fun strip => (InCritStrip_boundary_excluded strip).left (hsame_refl BHist.Empty)))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      have sameEmpty : hsame k BHist.Empty :=
        hsame_trans (hsame_symm same) carrier.left
      exact And.intro sameEmpty
        (fun strip => (InCritStrip_boundary_excluded strip).left sameEmpty)
  · intro _h source
    exact source
  · intro _h source
    exact source

theorem crit_strip_name_certificate :
    NameCert (fun h : BHist => hsame h BHist.Empty ∧ (InCritStrip h -> False))
        (fun h k : BHist => hsame h k) ∧
      (forall {s sigma tau : BHist}, CritStripComplexCarrier s sigma tau -> False) := by
  constructor
  · exact CritStripEmptyBoundary_semanticNameCert.core
  · intro s sigma tau carrier
    exact (CritStripComplexCarrier_strict_interval_absurd carrier).right

theorem crit_strip_semantic_name_certificate :
    SemanticNameCert
      (fun h : BHist =>
        hsame h BHist.Empty ∧
          (forall sigma tau : BHist, CritStripComplexCarrier h sigma tau -> False))
      (fun h : BHist =>
        hsame h BHist.Empty ∧
          (forall sigma tau : BHist, CritStripComplexCarrier h sigma tau -> False))
      (fun h : BHist =>
        hsame h BHist.Empty ∧
          (forall sigma tau : BHist, CritStripComplexCarrier h sigma tau -> False))
      hsame := by
  constructor
  · constructor
    · exact Exists.intro BHist.Empty
        (And.intro (hsame_refl BHist.Empty)
          (fun _sigma _tau carrier =>
            (CritStripComplexCarrier_strict_interval_absurd carrier).right))
    · intro h _carrier
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same carrier
      have sameEmpty : hsame k BHist.Empty :=
        hsame_trans (hsame_symm same) carrier.left
      exact And.intro sameEmpty
        (fun _sigma _tau obstruction =>
          (CritStripComplexCarrier_strict_interval_absurd obstruction).right)
  · intro _h source
    exact source
  · intro _h source
    exact source

end BEDC.Derived.CritStripUp
