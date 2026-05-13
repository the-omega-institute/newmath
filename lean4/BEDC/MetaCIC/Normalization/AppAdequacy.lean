import BEDC.MetaCIC.Normalization.Reducibility
import BEDC.MetaCIC.Normalization.PiAdequacy
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.SubjectReduction.ClosedDischarge

namespace BEDC.MetaCIC

theorem app_case_candidate
    {dom cod f a : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a) :
    Candidate (substitute 0 a cod) (Term.app f a) := by
  cases hf with
  | mk _ appCandidate =>
      exact appCandidate a ha

theorem app_case_candidate_from_pi_candidate
    {dom cod f a : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a) :
    Candidate (substitute 0 a cod) (Term.app f a) := by
  exact app_case_candidate hf ha

theorem app_case_sn_from_pi_candidate
    {dom cod f a : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a) :
    StrongNormalizable (Term.app f a) := by
  exact candidate_implies_sn
    (substitute 0 a cod)
    (Term.app f a)
    (app_case_candidate hf ha)

theorem app_case_sn_from_candidate
    {dom cod f a : Term}
    (hf : Candidate (Term.pi dom cod) f)
    (ha : Candidate dom a) :
    StrongNormalizable (Term.app f a) := by
  exact pi_candidate_app_sn hf ha

theorem app_case_candidate_step
    {dom cod f a r : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a)
    (hstep : BetaStep (Term.app f a) r) :
    Candidate (substitute 0 a cod) r := by
  exact candidate_closed_under_beta
    (substitute 0 a cod)
    (Term.app f a)
    r
    (app_case_candidate hf ha)
    hstep

theorem app_case_step_sn
    {dom cod f a r : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a)
    (hstep : BetaStep (Term.app f a) r) :
    StrongNormalizable r := by
  exact candidate_implies_sn
    (substitute 0 a cod)
    r
    (app_case_candidate_step hf ha hstep)

theorem app_case_beta_path_two_candidate
    {dom cod f a r s : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a)
    (hstep₁ : BetaStep (Term.app f a) r)
    (hstep₂ : BetaStep r s) :
    Candidate (substitute 0 a cod) s := by
  exact candidate_beta_path_two
    (app_case_candidate hf ha)
    hstep₁
    hstep₂

theorem app_case_beta_path_two_sn
    {dom cod f a r s : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a)
    (hstep₁ : BetaStep (Term.app f a) r)
    (hstep₂ : BetaStep r s) :
    StrongNormalizable s := by
  exact candidate_implies_sn
    (substitute 0 a cod)
    s
    (app_case_beta_path_two_candidate hf ha hstep₁ hstep₂)

theorem app_case_closed_term
    {dom cod f a : Term}
    (_hf : PiCandidate dom cod f)
    (_ha : Candidate dom a)
    (hfclosed : ClosedAt 0 f)
    (haclosed : ClosedAt 0 a) :
    ClosedAt 0 (Term.app f a) := by
  exact ClosedAt.appClosed hfclosed haclosed

theorem app_case_closed_step
    {dom cod f a r : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a)
    (hfclosed : ClosedAt 0 f)
    (haclosed : ClosedAt 0 a)
    (hstep : BetaStep (Term.app f a) r) :
    ClosedAt 0 r := by
  exact betaStep_preserves_closed
    (app_case_closed_term hf ha hfclosed haclosed)
    hstep

theorem app_case_closed_candidate_step
    {dom cod f a r : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a)
    (hclosedType : ClosedAt 0 (substitute 0 a cod))
    (hfclosed : ClosedAt 0 f)
    (haclosed : ClosedAt 0 a)
    (hstep : BetaStep (Term.app f a) r) :
    ClosedCandidate (substitute 0 a cod) r := by
  apply ClosedCandidate.mk
  · exact hclosedType
  · exact app_case_closed_step hf ha hfclosed haclosed hstep
  · exact app_case_candidate_step hf ha hstep

theorem app_sn_closed
    {dom cod f a : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a) :
    StrongNormalizable (Term.app f a) := by
  exact app_case_sn_from_pi_candidate hf ha

theorem app_sn_closed_from_closed_pi_candidate
    {dom cod f a : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a)
    (_hfclosed : ClosedAt 0 f)
    (_haclosed : ClosedAt 0 a) :
    StrongNormalizable (Term.app f a) := by
  exact app_sn_closed hf ha

theorem app_sn_closed_from_closed_candidate
    {dom cod f a : Term}
    (hf : Candidate (Term.pi dom cod) f)
    (ha : Candidate dom a)
    (_hfclosed : ClosedAt 0 f)
    (_haclosed : ClosedAt 0 a) :
    StrongNormalizable (Term.app f a) := by
  exact app_case_sn_from_candidate hf ha

theorem neutral_app_case_sn
    {f a : Term}
    (hfneutral : NeutralNormal f)
    (ha : StrongNormalizable a) :
    StrongNormalizable (Term.app f a) := by
  exact neutralApp_sn hfneutral ha

theorem neutral_app_case_step_sn
    {f a r : Term}
    (hfneutral : NeutralNormal f)
    (ha : StrongNormalizable a)
    (hstep : BetaStep (Term.app f a) r) :
    StrongNormalizable r := by
  exact strongNormalizable_step
    (neutral_app_case_sn hfneutral ha)
    hstep

theorem neutral_closed_app_sn
    {f a : Term}
    (hfneutral : NeutralNormal f)
    (_hfclosed : ClosedAt 0 f)
    (_haclosed : ClosedAt 0 a)
    (ha : StrongNormalizable a) :
    StrongNormalizable (Term.app f a) := by
  exact neutral_app_case_sn hfneutral ha

theorem candidate_pi_head_app_sn
    {dom cod f a : Term}
    (hf : Candidate (Term.pi dom cod) f)
    (ha : Candidate dom a) :
    StrongNormalizable (Term.app f a) := by
  exact app_case_sn_from_candidate hf ha

theorem pi_candidate_app_candidate_sound
    {dom cod f a : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a) :
    StrongNormalizable (Term.app f a) := by
  exact app_case_sn_from_pi_candidate hf ha

theorem pi_candidate_app_candidate_beta_closed
    {dom cod f a r : Term}
    (hf : PiCandidate dom cod f)
    (ha : Candidate dom a)
    (hstep : BetaStep (Term.app f a) r) :
    Candidate (substitute 0 a cod) r := by
  exact app_case_candidate_step hf ha hstep

theorem candidate_var_six_app
    {u : Term}
    (hu : Candidate Term.sort u) :
    Candidate (substitute 0 u (Term.var 7))
      (Term.app (Term.var 0) u) := by
  apply Candidate.mk
  · exact pi_candidate_app_sn
      (var_candidate (Term.pi Term.sort (Term.var 7)) 0)
      hu
  · change CandidateHead (Term.var 6) (Term.app (Term.var 0) u)
    exact CandidateHead.var 6 (Term.app (Term.var 0) u)

theorem var_zero_pi_candidate :
    PiCandidate Term.sort (Term.var 7) (Term.var 0) := by
  apply PiCandidate.mk
  · exact var_candidate (Term.pi Term.sort (Term.var 7)) 0
  · intro u hu
    exact candidate_var_six_app hu

theorem var_zero_sort_app_candidate :
    Candidate (substitute 0 Term.sort (Term.var 7))
      (Term.app (Term.var 0) Term.sort) := by
  exact app_case_candidate var_zero_pi_candidate sort_candidate

theorem var_zero_sort_app_sn :
    StrongNormalizable (Term.app (Term.var 0) Term.sort) := by
  exact app_sn_closed var_zero_pi_candidate sort_candidate

theorem var_zero_sort_app_step_candidate
    {r : Term}
    (hstep : BetaStep (Term.app (Term.var 0) Term.sort) r) :
    Candidate (substitute 0 Term.sort (Term.var 7)) r := by
  exact app_case_candidate_step
    var_zero_pi_candidate
    sort_candidate
    hstep

theorem var_zero_sort_app_step_sn
    {r : Term}
    (hstep : BetaStep (Term.app (Term.var 0) Term.sort) r) :
    StrongNormalizable r := by
  exact app_case_step_sn
    var_zero_pi_candidate
    sort_candidate
    hstep

def churchIdentityAtSortApp : Term :=
  Term.app churchIdentityTm Term.sort

theorem churchIdentityAtSortApp_type :
    HasType [] churchIdentityAtSortApp
      (substitute 0 Term.sort (Term.pi (Term.var 0) (Term.var 1))) := by
  unfold churchIdentityAtSortApp
  exact HasType.appRule []
    churchIdentityTm
    Term.sort
    Term.sort
    (Term.pi (Term.var 0) (Term.var 1))
    church_identity
    (HasType.sortRule [])

theorem churchIdentityAtSortApp_closed :
    ClosedAt 0 churchIdentityAtSortApp := by
  unfold churchIdentityAtSortApp
  unfold churchIdentityTm
  apply ClosedAt.appClosed
  · apply ClosedAt.lamClosed
    · exact ClosedAt.sortClosed
    · apply ClosedAt.lamClosed
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 0
      · apply ClosedAt.varClosed
        exact Nat.zero_lt_succ 1
  · exact ClosedAt.sortClosed

theorem churchIdentityAtSortApp_sn :
    StrongNormalizable churchIdentityAtSortApp := by
  unfold churchIdentityAtSortApp
  apply StrongNormalizable.mk
  intro r hstep
  cases hstep with
  | beta dom body arg =>
      change StrongNormalizable (Term.lam Term.sort (Term.var 0))
      exact sn_lam sort_is_sn (var_is_sn 0)
  | congApp1 f f' a hff' =>
      unfold churchIdentityTm at hff'
      cases hff' with
      | congLam d b b' hbb' =>
          cases hbb' with
          | congLam d b b' hbb'' =>
              cases hbb''
          | congLamDom d d' b hdd' =>
              cases hdd'
      | congLamDom d d' b hdd' =>
          cases hdd'
  | congApp2 f a a' haa' =>
      cases haa'

def selfApplyLam : Term :=
  Term.lam Term.sort (Term.app (Term.var 0) (Term.var 0))

def selfApplyApp : Term :=
  Term.app selfApplyLam selfApplyLam

theorem selfApplyLam_sn :
    StrongNormalizable selfApplyLam := by
  unfold selfApplyLam
  apply sn_lam
  · exact sort_is_sn
  · exact neutralApp_sn (NeutralNormal.var 0) (var_is_sn 0)

theorem selfApplyArg_sn :
    StrongNormalizable selfApplyLam := by
  exact selfApplyLam_sn

theorem selfApplyApp_step_self :
    BetaStep selfApplyApp selfApplyApp := by
  unfold selfApplyApp
  unfold selfApplyLam
  change
    BetaStep
      (Term.app
        (Term.lam Term.sort (Term.app (Term.var 0) (Term.var 0)))
        (Term.lam Term.sort (Term.app (Term.var 0) (Term.var 0))))
      (substitute 0
        (Term.lam Term.sort (Term.app (Term.var 0) (Term.var 0)))
        (Term.app (Term.var 0) (Term.var 0)))
  exact BetaStep.beta Term.sort
    (Term.app (Term.var 0) (Term.var 0))
    (Term.lam Term.sort (Term.app (Term.var 0) (Term.var 0)))

theorem strongNormalizable_no_self_step
    {t : Term}
    (hsn : StrongNormalizable t)
    (hstep : BetaStep t t) :
    False := by
  induction hsn with
  | mk t _ ih =>
      exact ih t hstep hstep

theorem selfApplyApp_not_sn :
    StrongNormalizable selfApplyApp → False := by
  intro hsn
  exact strongNormalizable_no_self_step hsn selfApplyApp_step_self

theorem app_sn_from_parts_is_not_unconditional :
    (StrongNormalizable selfApplyLam →
      StrongNormalizable selfApplyLam →
      StrongNormalizable selfApplyApp) → False := by
  intro h
  exact selfApplyApp_not_sn (h selfApplyLam_sn selfApplyArg_sn)

end BEDC.MetaCIC
