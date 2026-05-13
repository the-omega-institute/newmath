import BEDC.MetaCIC.Normalization.Reducibility
import BEDC.MetaCIC.Normalization.PiAdequacy
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.ClosurePreservation
import BEDC.MetaCIC.SubjectReduction.ClosedDischarge
import BEDC.MetaCIC.SubjectReduction.ClosedBinderDischarge

namespace BEDC.MetaCIC

def ClosedTypedTerm (t A : Term) : Prop :=
  HasType [] t A ∧ ClosedAt 0 t

def ClosedTypedCandidate (t A : Term) : Prop :=
  ClosedTypedTerm t A ∧ Candidate A t

def ClosedTypedPiCandidate (f dom cod : Term) : Prop :=
  ClosedTypedTerm f (Term.pi dom cod) ∧ PiCandidate dom cod f

def ClosedTypedCandidateSetMember (t A : Term) (C : CandidateSet A) : Prop :=
  ClosedTypedTerm t A ∧ C.member t

theorem closedTypedTerm_typed {t A : Term}
    (h : ClosedTypedTerm t A) :
    HasType [] t A := by
  exact h.left

theorem closedTypedTerm_closed {t A : Term}
    (h : ClosedTypedTerm t A) :
    ClosedAt 0 t := by
  exact h.right

theorem closedTypedCandidate_closedTyped {t A : Term}
    (h : ClosedTypedCandidate t A) :
    ClosedTypedTerm t A := by
  exact h.left

theorem closedTypedCandidate_candidate {t A : Term}
    (h : ClosedTypedCandidate t A) :
    Candidate A t := by
  exact h.right

theorem closedTypedCandidate_typed {t A : Term}
    (h : ClosedTypedCandidate t A) :
    HasType [] t A := by
  exact closedTypedTerm_typed (closedTypedCandidate_closedTyped h)

theorem closedTypedCandidate_closed {t A : Term}
    (h : ClosedTypedCandidate t A) :
    ClosedAt 0 t := by
  exact closedTypedTerm_closed (closedTypedCandidate_closedTyped h)

theorem closedTypedCandidate_implies_sn {t A : Term}
    (h : ClosedTypedCandidate t A) :
    StrongNormalizable t := by
  exact candidate_implies_sn A t (closedTypedCandidate_candidate h)

theorem closedTypedCandidateSetMember_closedTyped {t A : Term}
    {C : CandidateSet A}
    (h : ClosedTypedCandidateSetMember t A C) :
    ClosedTypedTerm t A := by
  exact h.left

theorem closedTypedCandidateSetMember_member {t A : Term}
    {C : CandidateSet A}
    (h : ClosedTypedCandidateSetMember t A C) :
    C.member t := by
  exact h.right

theorem closedTypedCandidateSetMember_implies_sn {t A : Term}
    {C : CandidateSet A}
    (h : ClosedTypedCandidateSetMember t A C) :
    StrongNormalizable t := by
  exact C.sound t (closedTypedCandidateSetMember_member h)

theorem closedTypedPiCandidate_closedTyped {f dom cod : Term}
    (h : ClosedTypedPiCandidate f dom cod) :
    ClosedTypedTerm f (Term.pi dom cod) := by
  exact h.left

theorem closedTypedPiCandidate_piCandidate {f dom cod : Term}
    (h : ClosedTypedPiCandidate f dom cod) :
    PiCandidate dom cod f := by
  exact h.right

theorem closedTypedPiCandidate_implies_sn {f dom cod : Term}
    (h : ClosedTypedPiCandidate f dom cod) :
    StrongNormalizable f := by
  exact piCandidate_implies_sn (closedTypedPiCandidate_piCandidate h)

theorem closedTypedPiCandidate_candidate {f dom cod : Term}
    (h : ClosedTypedPiCandidate f dom cod) :
    Candidate (Term.pi dom cod) f := by
  exact piCandidate_implies_candidate (closedTypedPiCandidate_piCandidate h)

theorem closedTypedPiCandidate_app_candidate {f dom cod u : Term}
    (hf : ClosedTypedPiCandidate f dom cod)
    (hu : Candidate dom u) :
    Candidate (substitute 0 u cod) (Term.app f u) := by
  exact pi_candidate_app (closedTypedPiCandidate_piCandidate hf) hu

theorem closedTypedPiCandidate_app_sn {f dom cod u : Term}
    (hf : ClosedTypedPiCandidate f dom cod)
    (hu : Candidate dom u) :
    StrongNormalizable (Term.app f u) := by
  exact candidate_implies_sn (substitute 0 u cod) (Term.app f u)
    (closedTypedPiCandidate_app_candidate hf hu)

theorem closedTypedPiCandidate_app_step_candidate
    {f dom cod u r : Term}
    (hf : ClosedTypedPiCandidate f dom cod)
    (hu : Candidate dom u)
    (hstep : BetaStep (Term.app f u) r) :
    Candidate (substitute 0 u cod) r := by
  exact candidate_closed_under_beta
    (substitute 0 u cod)
    (Term.app f u)
    r
    (closedTypedPiCandidate_app_candidate hf hu)
    hstep

theorem closedTypedPiCandidate_app_step_sn
    {f dom cod u r : Term}
    (hf : ClosedTypedPiCandidate f dom cod)
    (hu : Candidate dom u)
    (hstep : BetaStep (Term.app f u) r) :
    StrongNormalizable r := by
  exact candidate_implies_sn (substitute 0 u cod) r
    (closedTypedPiCandidate_app_step_candidate hf hu hstep)

theorem closedTypedTerm_step_closed {t t' A : Term}
    (h : ClosedTypedTerm t A)
    (hstep : BetaStep t t') :
    ClosedAt 0 t' := by
  exact betaStep_preserves_closed (closedTypedTerm_closed h) hstep

theorem closedTypedCandidate_step_candidate {t t' A : Term}
    (h : ClosedTypedCandidate t A)
    (hstep : BetaStep t t') :
    Candidate A t' := by
  exact candidate_closed_under_beta A t t'
    (closedTypedCandidate_candidate h)
    hstep

theorem closedTypedCandidate_step_sn {t t' A : Term}
    (h : ClosedTypedCandidate t A)
    (hstep : BetaStep t t') :
    StrongNormalizable t' := by
  exact candidate_implies_sn A t'
    (closedTypedCandidate_step_candidate h hstep)

theorem closedTypedCandidate_step_closedCandidate
    {t t' A : Term}
    (hclosedA : ClosedAt 0 A)
    (h : ClosedTypedCandidate t A)
    (hstep : BetaStep t t') :
    ClosedCandidate A t' := by
  apply ClosedCandidate.mk
  · exact hclosedA
  · exact closedTypedTerm_step_closed
      (closedTypedCandidate_closedTyped h)
      hstep
  · exact closedTypedCandidate_step_candidate h hstep

theorem closedCandidate_to_closedTypedCandidate {t A : Term}
    (ht : HasType [] t A)
    (h : ClosedCandidate A t) :
    ClosedTypedCandidate t A := by
  apply And.intro
  · apply And.intro
    · exact ht
    · exact closedCandidate_closedTerm h
  · exact closedCandidate_candidate h

theorem closedTypedCandidate_to_closedCandidate {t A : Term}
    (hclosedA : ClosedAt 0 A)
    (h : ClosedTypedCandidate t A) :
    ClosedCandidate A t := by
  apply ClosedCandidate.mk
  · exact hclosedA
  · exact closedTypedCandidate_closed h
  · exact closedTypedCandidate_candidate h

theorem closed_typed_term_sn_from_candidate :
    ∀ {t A}, HasType [] t A → ClosedAt 0 t →
      Candidate A t → StrongNormalizable t := by
  intro t A _ht _hclosed hcand
  exact candidate_implies_sn A t hcand

theorem closed_typed_term_sn_from_closedCandidate :
    ∀ {t A}, HasType [] t A → ClosedCandidate A t →
      StrongNormalizable t := by
  intro t A _ht hcandidate
  exact closedCandidate_implies_sn hcandidate

theorem closed_typed_term_sn_from_candidateSet :
    ∀ {t A} (C : CandidateSet A), HasType [] t A → ClosedAt 0 t →
      C.member t → StrongNormalizable t := by
  intro t A C _ht _hclosed hmember
  exact C.sound t hmember

theorem closed_typed_pi_term_sn_from_piCandidate :
    ∀ {f dom cod}, HasType [] f (Term.pi dom cod) → ClosedAt 0 f →
      PiCandidate dom cod f → StrongNormalizable f := by
  intro f dom cod _ht _hclosed hpi
  exact piCandidate_implies_sn hpi

theorem closed_typed_pi_app_sn_from_piCandidate :
    ∀ {f dom cod u}, HasType [] f (Term.pi dom cod) → ClosedAt 0 f →
      PiCandidate dom cod f → Candidate dom u →
      StrongNormalizable (Term.app f u) := by
  intro f dom cod u _ht _hclosed hpi hu
  exact piCandidate_head_sn hpi hu

theorem closed_sort_closedTypedTerm :
    ClosedTypedTerm Term.sort Term.sort := by
  apply And.intro
  · exact HasType.sortRule []
  · exact ClosedAt.sortClosed

theorem closed_sort_closedTypedCandidate :
    ClosedTypedCandidate Term.sort Term.sort := by
  apply And.intro
  · exact closed_sort_closedTypedTerm
  · exact sort_candidate

theorem closed_sort_sn :
    StrongNormalizable Term.sort := by
  exact closedTypedCandidate_implies_sn closed_sort_closedTypedCandidate

theorem closed_sort_no_step {t' : Term} :
    BetaStep Term.sort t' → False := by
  intro hstep
  exact sort_no_betaStrong_successor hstep

theorem closed_empty_var_absurd {i : Idx} :
    ClosedAt 0 (Term.var i) → False := by
  intro h
  cases h with
  | varClosed hlt =>
      exact Nat.not_lt_zero i hlt

theorem empty_ctx_var_typed_absurd {i : Idx} {A : Term} :
    HasType [] (Term.var i) A → False := by
  intro h
  cases h with
  | varRule Γ j B hlookup =>
      cases hlookup

theorem closed_empty_var_candidate_sn {i : Idx}
    (hclosed : ClosedAt 0 (Term.var i)) :
    StrongNormalizable (Term.var i) := by
  exact False.elim (closed_empty_var_absurd hclosed)

theorem closed_empty_var_typed_sn {i : Idx} {A : Term}
    (ht : HasType [] (Term.var i) A)
    (_hclosed : ClosedAt 0 (Term.var i)) :
    StrongNormalizable (Term.var i) := by
  exact False.elim (empty_ctx_var_typed_absurd ht)

theorem closed_lam_sn_from_parts {dom body : Term}
    (hdom : StrongNormalizable dom)
    (hbody : StrongNormalizable body) :
    StrongNormalizable (Term.lam dom body) := by
  exact sn_lam hdom hbody

theorem closed_pi_sn_from_parts {dom cod : Term}
    (hdom : StrongNormalizable dom)
    (hcod : StrongNormalizable cod) :
    StrongNormalizable (Term.pi dom cod) := by
  exact sn_pi hdom hcod

theorem neutral_closed_app_sn_from_parts {f a : Term}
    (hfneutral : NeutralNormal f)
    (ha : StrongNormalizable a) :
    StrongNormalizable (Term.app f a) := by
  exact neutralApp_sn hfneutral ha

theorem closed_neutral_candidate_sn {t A : Term}
    (_ht : HasType [] t A)
    (_hclosed : ClosedAt 0 t)
    (_hneutral : NeutralNormal t)
    (hcand : Candidate A t) :
    StrongNormalizable t := by
  exact candidate_implies_sn A t hcand

theorem closed_neutral_sn {t A : Term}
    (_ht : HasType [] t A)
    (_hclosed : ClosedAt 0 t)
    (hneutral : NeutralNormal t) :
    StrongNormalizable t := by
  exact neutralNormal_implies_sn hneutral

theorem candidate_head_for_closed_sort {t : Term}
    (h : ClosedTypedCandidate t Term.sort) :
    CandidateHead Term.sort t := by
  exact candidate_head (closedTypedCandidate_candidate h)

theorem candidate_head_for_closed_pi {dom cod f : Term}
    (h : ClosedTypedCandidate f (Term.pi dom cod)) :
    ∀ u, StrongNormalizable u →
      StrongNormalizable (Term.app f u) := by
  exact candidate_pi_type_head (closedTypedCandidate_candidate h)

theorem closed_candidate_set_step_member {t t' A : Term}
    (C : CandidateSet A)
    (h : ClosedTypedCandidateSetMember t A C)
    (hstep : BetaStep t t') :
    C.member t' := by
  exact C.betaClosed t t'
    (closedTypedCandidateSetMember_member h)
    hstep

theorem closed_candidate_set_step_sn {t t' A : Term}
    (C : CandidateSet A)
    (h : ClosedTypedCandidateSetMember t A C)
    (hstep : BetaStep t t') :
    StrongNormalizable t' := by
  exact C.sound t'
    (closed_candidate_set_step_member C h hstep)

theorem closed_candidate_set_step_closed {t t' A : Term}
    (C : CandidateSet A)
    (h : ClosedTypedCandidateSetMember t A C)
    (hstep : BetaStep t t') :
    ClosedAt 0 t' := by
  exact betaStep_preserves_closed
    (closedTypedTerm_closed
      (closedTypedCandidateSetMember_closedTyped h))
    hstep

theorem closed_candidate_set_closed_step_member {t t' A : Term}
    (C : CandidateSet A)
    (h : ClosedTypedCandidateSetMember t A C)
    (hstep : BetaStep t t') :
    C.closedMember t' := by
  apply And.intro
  · exact closed_candidate_set_step_closed C h hstep
  · exact closed_candidate_set_step_member C h hstep

theorem sn_tail_of_step {t t' : Term}
    (hsn : StrongNormalizable t)
    (hstep : BetaStep t t') :
    StrongNormalizable t' := by
  exact strongNormalizable_step hsn hstep

theorem strongNormalizable_no_infinite_reduction :
    ∀ {t}, StrongNormalizable t →
      ¬ ∃ (chain : Nat → Term),
        chain 0 = t ∧ ∀ n, BetaStep (chain n) (chain (n + 1)) := by
  intro t hsn
  induction hsn with
  | mk t hnext ih =>
      intro hbad
      cases hbad with
      | intro chain hchain =>
          have hzero : BetaStep t (chain (0 + 1)) := by
            rw [← hchain.left]
            exact hchain.right 0
          have htail :
              ∃ (tail : Nat → Term),
                tail 0 = chain (0 + 1) ∧
                  ∀ n, BetaStep (tail n) (tail (n + 1)) := by
            exact
              Exists.intro
                (fun n => chain (n + 1))
                (And.intro rfl
                  (by
                    intro n
                    exact hchain.right (n + 1)))
          exact ih (chain (0 + 1)) hzero htail

theorem candidate_no_infinite_reduction {t A : Term}
    (h : Candidate A t) :
    ¬ ∃ (chain : Nat → Term),
      chain 0 = t ∧ ∀ n, BetaStep (chain n) (chain (n + 1)) := by
  exact strongNormalizable_no_infinite_reduction
    (candidate_implies_sn A t h)

theorem closedCandidate_no_infinite_reduction {t A : Term}
    (h : ClosedCandidate A t) :
    ¬ ∃ (chain : Nat → Term),
      chain 0 = t ∧ ∀ n, BetaStep (chain n) (chain (n + 1)) := by
  exact strongNormalizable_no_infinite_reduction
    (closedCandidate_implies_sn h)

theorem closedTypedCandidate_no_infinite_reduction {t A : Term}
    (h : ClosedTypedCandidate t A) :
    ¬ ∃ (chain : Nat → Term),
      chain 0 = t ∧ ∀ n, BetaStep (chain n) (chain (n + 1)) := by
  exact strongNormalizable_no_infinite_reduction
    (closedTypedCandidate_implies_sn h)

theorem closed_typed_term_no_infinite_reduction_from_candidate :
    ∀ {t A} (_hT : HasType [] t A) (_h : ClosedAt 0 t),
      Candidate A t →
      ¬ ∃ (chain : Nat → Term),
        chain 0 = t ∧ ∀ n, BetaStep (chain n) (chain (n + 1)) := by
  intro t A _hT _hclosed hcand
  exact candidate_no_infinite_reduction hcand

theorem closed_typed_term_no_infinite_reduction_from_closedCandidate :
    ∀ {t A} (_hT : HasType [] t A),
      ClosedCandidate A t →
      ¬ ∃ (chain : Nat → Term),
        chain 0 = t ∧ ∀ n, BetaStep (chain n) (chain (n + 1)) := by
  intro t A _hT hcandidate
  exact closedCandidate_no_infinite_reduction hcandidate

theorem closed_typed_term_no_infinite_reduction_from_candidateSet :
    ∀ {t A} (C : CandidateSet A)
      (_hT : HasType [] t A) (_h : ClosedAt 0 t),
      C.member t →
      ¬ ∃ (chain : Nat → Term),
        chain 0 = t ∧ ∀ n, BetaStep (chain n) (chain (n + 1)) := by
  intro t A C _hT _hclosed hmember
  exact strongNormalizable_no_infinite_reduction
    (C.sound t hmember)

theorem closed_sort_no_infinite_reduction :
    ¬ ∃ (chain : Nat → Term),
      chain 0 = Term.sort ∧ ∀ n, BetaStep (chain n) (chain (n + 1)) := by
  exact strongNormalizable_no_infinite_reduction sort_is_sn

theorem closed_lam_no_infinite_reduction_from_parts {dom body : Term}
    (hdom : StrongNormalizable dom)
    (hbody : StrongNormalizable body) :
    ¬ ∃ (chain : Nat → Term),
      chain 0 = Term.lam dom body ∧
        ∀ n, BetaStep (chain n) (chain (n + 1)) := by
  exact strongNormalizable_no_infinite_reduction
    (sn_lam hdom hbody)

theorem closed_pi_no_infinite_reduction_from_parts {dom cod : Term}
    (hdom : StrongNormalizable dom)
    (hcod : StrongNormalizable cod) :
    ¬ ∃ (chain : Nat → Term),
      chain 0 = Term.pi dom cod ∧
        ∀ n, BetaStep (chain n) (chain (n + 1)) := by
  exact strongNormalizable_no_infinite_reduction
    (sn_pi hdom hcod)

theorem closed_neutral_no_infinite_reduction {t A : Term}
    (ht : HasType [] t A)
    (hclosed : ClosedAt 0 t)
    (hneutral : NeutralNormal t) :
    ¬ ∃ (chain : Nat → Term),
      chain 0 = t ∧ ∀ n, BetaStep (chain n) (chain (n + 1)) := by
  exact strongNormalizable_no_infinite_reduction
    (closed_neutral_sn ht hclosed hneutral)

theorem closedTypedCandidate_beta_path_two_sn
    {t t' t'' A : Term}
    (h : ClosedTypedCandidate t A)
    (hstep₁ : BetaStep t t')
    (hstep₂ : BetaStep t' t'') :
    StrongNormalizable t'' := by
  exact candidate_implies_sn A t''
    (candidate_beta_path_two
      (closedTypedCandidate_candidate h)
      hstep₁
      hstep₂)

theorem closedTypedCandidate_beta_path_two_closed
    {t t' t'' A : Term}
    (h : ClosedTypedCandidate t A)
    (hstep₁ : BetaStep t t')
    (hstep₂ : BetaStep t' t'') :
    ClosedAt 0 t'' := by
  exact betaStep_preserves_closed
    (betaStep_preserves_closed
      (closedTypedCandidate_closed h)
      hstep₁)
    hstep₂

theorem closedTypedCandidate_beta_path_two_closedCandidate
    {t t' t'' A : Term}
    (hclosedA : ClosedAt 0 A)
    (h : ClosedTypedCandidate t A)
    (hstep₁ : BetaStep t t')
    (hstep₂ : BetaStep t' t'') :
    ClosedCandidate A t'' := by
  apply ClosedCandidate.mk
  · exact hclosedA
  · exact closedTypedCandidate_beta_path_two_closed h hstep₁ hstep₂
  · exact candidate_beta_path_two
      (closedTypedCandidate_candidate h)
      hstep₁
      hstep₂

theorem closedTypedCandidate_canonicalSet_member {t A : Term}
    (h : ClosedTypedCandidate t A) :
    (canonicalCandidateSet A).member t := by
  exact closedTypedCandidate_candidate h

theorem closedTypedCandidate_snSet_member {t A : Term}
    (h : ClosedTypedCandidate t A) :
    (snCandidateSet A).member t := by
  exact closedTypedCandidate_implies_sn h

theorem closedTypedCandidate_canonicalSet_closedMember {t A : Term}
    (h : ClosedTypedCandidate t A) :
    (canonicalCandidateSet A).closedMember t := by
  apply And.intro
  · exact closedTypedCandidate_closed h
  · exact closedTypedCandidate_candidate h

theorem closedTypedCandidate_snSet_closedMember {t A : Term}
    (h : ClosedTypedCandidate t A) :
    (snCandidateSet A).closedMember t := by
  apply And.intro
  · exact closedTypedCandidate_closed h
  · exact closedTypedCandidate_implies_sn h

end BEDC.MetaCIC
