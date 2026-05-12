import BEDC.MetaCIC.Syntax
import BEDC.MetaCIC.Beta
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

def BetaStrong (t : Term) : Prop :=
  ¬ ∃ t', BetaStep t t'

inductive StrongNormalizable : Term → Prop
  | mk (t : Term) (h : ∀ t', BetaStep t t' → StrongNormalizable t') :
      StrongNormalizable t

def Term.structSize : Term → Nat
  | Term.var _ => 1
  | Term.app f a => Term.structSize f + Term.structSize a + 1
  | Term.lam dom body => Term.structSize dom + Term.structSize body + 1
  | Term.pi dom cod => Term.structSize dom + Term.structSize cod + 1
  | Term.sort => 1

inductive CandidateHead : Term → Term → Prop
  | var (i : Idx) (t : Term) :
      CandidateHead (Term.var i) t
  | app (f a t : Term) :
      CandidateHead (Term.app f a) t
  | lam (dom body t : Term) :
      CandidateHead (Term.lam dom body) t
  | pi (dom cod t : Term)
      (appSN : ∀ u, StrongNormalizable u →
        StrongNormalizable (Term.app t u)) :
      CandidateHead (Term.pi dom cod) t
  | sort (t : Term) :
      CandidateHead Term.sort t

inductive Candidate : Term → Term → Prop
  | mk (A t : Term)
      (sn : StrongNormalizable t)
      (head : CandidateHead A t) :
      Candidate A t

inductive ClosedCandidate : Term → Term → Prop
  | mk (A t : Term)
      (closedType : ClosedAt 0 A)
      (closedTerm : ClosedAt 0 t)
      (candidate : Candidate A t) :
      ClosedCandidate A t

inductive PiCandidate : Term → Term → Term → Prop
  | mk (dom cod f : Term)
      (candidate : Candidate (Term.pi dom cod) f)
      (appCandidate :
        ∀ u, Candidate dom u →
          Candidate (substitute 0 u cod) (Term.app f u)) :
      PiCandidate dom cod f

structure CandidateSet (A : Term) : Type where
  member : Term → Prop
  sound : ∀ t, member t → StrongNormalizable t
  betaClosed : ∀ t t', member t → BetaStep t t' → member t'

def CandidateSet.closedMember {A : Term} (C : CandidateSet A) (t : Term) : Prop :=
  ClosedAt 0 t ∧ C.member t

def CandidateSet.closedSound {A : Term} (C : CandidateSet A) (t : Term)
    (h : C.closedMember t) :
    StrongNormalizable t :=
  C.sound t h.right

def CandidateSet.closedBeta {A : Term} (C : CandidateSet A) (t t' : Term)
    (hclosed : ClosedAt 0 t')
    (h : C.closedMember t)
    (hbeta : BetaStep t t') :
    C.closedMember t' :=
  And.intro hclosed (C.betaClosed t t' h.right hbeta)

def snCandidateSet (A : Term) : CandidateSet A where
  member := StrongNormalizable
  sound := by
    intro t h
    exact h
  betaClosed := by
    intro t t' h hbeta
    cases h with
    | mk _ hnext =>
        exact hnext t' hbeta

theorem strongNormalizable_step {t t' : Term}
    (h : StrongNormalizable t) (hbeta : BetaStep t t') :
    StrongNormalizable t' := by
  cases h with
  | mk _ hnext =>
      exact hnext t' hbeta

theorem strongNormalizable_reduces_once {t t' : Term}
    (hbeta : BetaStep t t') :
    StrongNormalizable t → StrongNormalizable t' := by
  intro h
  exact strongNormalizable_step h hbeta

theorem betaStrong_no_step {t t' : Term}
    (h : BetaStrong t) :
    BetaStep t t' → False := by
  intro hbeta
  apply h
  exact Exists.intro t' hbeta

theorem betaStrong_of_no_step {t : Term}
    (h : ∀ t', BetaStep t t' → False) :
    BetaStrong t := by
  intro hstep
  cases hstep with
  | intro t' hbeta =>
      exact h t' hbeta

theorem betaStrong_implies_sn {t : Term}
    (h : BetaStrong t) :
    StrongNormalizable t := by
  apply StrongNormalizable.mk
  intro t' hbeta
  exact False.elim (betaStrong_no_step h hbeta)

theorem sort_betaStrong : BetaStrong Term.sort := by
  intro hstep
  cases hstep with
  | intro t' hbeta =>
      cases hbeta

theorem var_betaStrong (i : Idx) : BetaStrong (Term.var i) := by
  intro hstep
  cases hstep with
  | intro t' hbeta =>
      cases hbeta

theorem sort_is_sn : StrongNormalizable Term.sort := by
  exact betaStrong_implies_sn sort_betaStrong

theorem var_is_sn (i : Idx) : StrongNormalizable (Term.var i) := by
  exact betaStrong_implies_sn (var_betaStrong i)

theorem betaStrong_app_of_no_head_no_arg {f a : Term}
    (h : ∀ r, BetaStep (Term.app f a) r → False) :
    BetaStrong (Term.app f a) := by
  exact betaStrong_of_no_step h

theorem candidate_implies_sn (A t : Term) (h : Candidate A t) :
    StrongNormalizable t := by
  cases h with
  | mk hsn _ =>
      exact hsn

theorem candidate_sn {A t : Term}
    (h : Candidate A t) :
    StrongNormalizable t := by
  exact candidate_implies_sn A t h

theorem candidate_head {A t : Term}
    (h : Candidate A t) :
    CandidateHead A t := by
  cases h with
  | mk _ hhead =>
      exact hhead

theorem app_candidate_head_step {A f f' : Term}
    (hhead : CandidateHead A f)
    (hbeta : BetaStep f f') :
    CandidateHead A f' := by
  cases A with
  | var i =>
      exact CandidateHead.var i f'
  | app g b =>
      exact CandidateHead.app g b f'
  | lam dom body =>
      exact CandidateHead.lam dom body f'
  | pi dom cod =>
      apply CandidateHead.pi
      intro u husn
      cases hhead with
      | pi _ _ _ appSN =>
          exact strongNormalizable_step
            (appSN u husn)
            (BetaStep.congApp1 f f' u hbeta)
  | sort =>
      exact CandidateHead.sort f'

theorem candidate_closed_under_beta (A t t' : Term)
    (hcand : Candidate A t) (hbeta : BetaStep t t') :
    Candidate A t' := by
  cases hcand with
  | mk hsn hhead =>
      apply Candidate.mk
      · exact strongNormalizable_step hsn hbeta
      · exact app_candidate_head_step hhead hbeta

theorem candidate_step_sn {A t t' : Term}
    (h : Candidate A t) (hbeta : BetaStep t t') :
    StrongNormalizable t' := by
  exact candidate_implies_sn A t'
    (candidate_closed_under_beta A t t' h hbeta)

theorem candidate_beta_path_two {A t t' t'' : Term}
    (h : Candidate A t)
    (hbeta₁ : BetaStep t t')
    (hbeta₂ : BetaStep t' t'') :
    Candidate A t'' := by
  exact candidate_closed_under_beta A t' t''
    (candidate_closed_under_beta A t t' h hbeta₁)
    hbeta₂

theorem candidate_sn_path_two {A t t' t'' : Term}
    (h : Candidate A t)
    (hbeta₁ : BetaStep t t')
    (hbeta₂ : BetaStep t' t'') :
    StrongNormalizable t'' := by
  exact candidate_implies_sn A t''
    (candidate_beta_path_two h hbeta₁ hbeta₂)

theorem var_app_sn (i : Idx) {u : Term}
    (h : StrongNormalizable u) :
    StrongNormalizable (Term.app (Term.var i) u) := by
  induction h with
  | mk u hnext ih =>
      apply StrongNormalizable.mk
      intro r hbeta
      cases hbeta with
      | congApp1 f f' a hff' =>
          cases hff'
      | congApp2 f a a' haa' =>
          exact ih a' haa'

theorem sort_candidateHead :
    CandidateHead Term.sort Term.sort := by
  exact CandidateHead.sort Term.sort

theorem var_candidateHead (A : Term) (i : Idx) :
    CandidateHead A (Term.var i) := by
  cases A with
  | var j =>
      exact CandidateHead.var j (Term.var i)
  | app f a =>
      exact CandidateHead.app f a (Term.var i)
  | lam dom body =>
      exact CandidateHead.lam dom body (Term.var i)
  | pi dom cod =>
      apply CandidateHead.pi
      intro u husn
      exact var_app_sn i husn
  | sort =>
      exact CandidateHead.sort (Term.var i)

theorem sort_candidate : Candidate Term.sort Term.sort := by
  apply Candidate.mk
  · exact sort_is_sn
  · exact sort_candidateHead

theorem var_candidate (A : Term) (i : Idx) :
    Candidate A (Term.var i) := by
  apply Candidate.mk
  · exact var_is_sn i
  · exact var_candidateHead A i

theorem candidate_sort_head {t : Term}
    (_h : Candidate Term.sort t) :
    CandidateHead Term.sort t := by
  exact CandidateHead.sort t

theorem candidate_var_type_head {i : Idx} {t : Term}
    (_h : Candidate (Term.var i) t) :
    CandidateHead (Term.var i) t := by
  exact CandidateHead.var i t

theorem candidate_app_type_head {f a t : Term}
    (_h : Candidate (Term.app f a) t) :
    CandidateHead (Term.app f a) t := by
  exact CandidateHead.app f a t

theorem candidate_lam_type_head {dom body t : Term}
    (_h : Candidate (Term.lam dom body) t) :
    CandidateHead (Term.lam dom body) t := by
  exact CandidateHead.lam dom body t

theorem candidate_pi_type_head {dom cod f : Term}
    (h : Candidate (Term.pi dom cod) f) :
    ∀ u, StrongNormalizable u →
      StrongNormalizable (Term.app f u) := by
  cases candidate_head h with
  | pi _ _ _ appSN =>
      exact appSN

theorem pi_candidate_app_sn {dom cod f u : Term}
    (hf : Candidate (Term.pi dom cod) f)
    (hu : Candidate dom u) :
    StrongNormalizable (Term.app f u) := by
  exact candidate_pi_type_head hf u (candidate_implies_sn dom u hu)

theorem pi_candidate_app
    {dom cod f u : Term}
    (hf : PiCandidate dom cod f)
    (hu : Candidate dom u) :
    Candidate (substitute 0 u cod) (Term.app f u) := by
  cases hf with
  | mk _ appCandidate =>
      exact appCandidate u hu

theorem pi_candidate_app_beta_closed
    {dom cod f u r : Term}
    (hf : PiCandidate dom cod f)
    (hu : Candidate dom u)
    (hbeta : BetaStep (Term.app f u) r) :
    Candidate (substitute 0 u cod) r := by
  exact candidate_closed_under_beta
    (substitute 0 u cod)
    (Term.app f u)
    r
    (pi_candidate_app hf hu)
    hbeta

theorem piCandidate_implies_candidate {dom cod f : Term}
    (h : PiCandidate dom cod f) :
    Candidate (Term.pi dom cod) f := by
  cases h with
  | mk hcand _ =>
      exact hcand

theorem piCandidate_implies_sn {dom cod f : Term}
    (h : PiCandidate dom cod f) :
    StrongNormalizable f := by
  exact candidate_implies_sn (Term.pi dom cod) f
    (piCandidate_implies_candidate h)

theorem piCandidate_head_sn {dom cod f u : Term}
    (h : PiCandidate dom cod f)
    (hu : Candidate dom u) :
    StrongNormalizable (Term.app f u) := by
  exact candidate_implies_sn
    (substitute 0 u cod)
    (Term.app f u)
    (pi_candidate_app h hu)

theorem closedCandidate_candidate {A t : Term}
    (h : ClosedCandidate A t) :
    Candidate A t := by
  cases h with
  | mk _ _ hcand =>
      exact hcand

theorem closedCandidate_closedType {A t : Term}
    (h : ClosedCandidate A t) :
    ClosedAt 0 A := by
  cases h with
  | mk hclosedType _ _ =>
      exact hclosedType

theorem closedCandidate_closedTerm {A t : Term}
    (h : ClosedCandidate A t) :
    ClosedAt 0 t := by
  cases h with
  | mk _ hclosedTerm _ =>
      exact hclosedTerm

theorem closedCandidate_implies_sn {A t : Term}
    (h : ClosedCandidate A t) :
    StrongNormalizable t := by
  exact candidate_implies_sn A t (closedCandidate_candidate h)

theorem closed_sort_candidate :
    ClosedCandidate Term.sort Term.sort := by
  apply ClosedCandidate.mk
  · exact ClosedAt.sortClosed
  · exact ClosedAt.sortClosed
  · exact sort_candidate

theorem closedCandidate_under_beta_with_closed_target
    {A t t' : Term}
    (h : ClosedCandidate A t)
    (hclosedTarget : ClosedAt 0 t')
    (hbeta : BetaStep t t') :
    ClosedCandidate A t' := by
  apply ClosedCandidate.mk
  · exact closedCandidate_closedType h
  · exact hclosedTarget
  · exact candidate_closed_under_beta A t t'
      (closedCandidate_candidate h)
      hbeta

theorem candidateSet_implies_sn {A t : Term}
    (C : CandidateSet A)
    (h : C.member t) :
    StrongNormalizable t := by
  exact C.sound t h

theorem candidateSet_closed_under_beta {A t t' : Term}
    (C : CandidateSet A)
    (h : C.member t)
    (hbeta : BetaStep t t') :
    C.member t' := by
  exact C.betaClosed t t' h hbeta

def canonicalCandidateSet (A : Term) : CandidateSet A where
  member := Candidate A
  sound := by
    intro t h
    exact candidate_implies_sn A t h
  betaClosed := by
    intro t t' h hbeta
    exact candidate_closed_under_beta A t t' h hbeta

theorem snCandidateSet_member_iff_left {A t : Term}
    (h : (snCandidateSet A).member t) :
    StrongNormalizable t := by
  exact h

theorem canonicalCandidateSet_member {A t : Term}
    (h : (canonicalCandidateSet A).member t) :
    Candidate A t := by
  exact h

theorem canonicalCandidateSet_sound {A t : Term}
    (h : (canonicalCandidateSet A).member t) :
    StrongNormalizable t := by
  exact candidate_implies_sn A t h

theorem canonicalCandidateSet_beta {A t t' : Term}
    (h : (canonicalCandidateSet A).member t)
    (hbeta : BetaStep t t') :
    (canonicalCandidateSet A).member t' := by
  exact candidate_closed_under_beta A t t' h hbeta

theorem sort_no_betaStrong_successor {t' : Term}
    (hbeta : BetaStep Term.sort t') :
    False := by
  exact betaStrong_no_step sort_betaStrong hbeta

theorem var_no_betaStrong_successor {i : Idx} {t' : Term}
    (hbeta : BetaStep (Term.var i) t') :
    False := by
  exact betaStrong_no_step (var_betaStrong i) hbeta

theorem sort_candidate_closed_under_beta {t' : Term}
    (hbeta : BetaStep Term.sort t') :
    Candidate Term.sort t' := by
  exact False.elim (sort_no_betaStrong_successor hbeta)

theorem var_candidate_closed_under_beta {A : Term} {i : Idx} {t' : Term}
    (hbeta : BetaStep (Term.var i) t') :
    Candidate A t' := by
  exact False.elim (var_no_betaStrong_successor hbeta)

theorem candidate_head_step {A t t' : Term}
    (h : Candidate A t)
    (hbeta : BetaStep t t') :
    CandidateHead A t' := by
  exact candidate_head (candidate_closed_under_beta A t t' h hbeta)

theorem candidate_with_betaStrong {A t : Term}
    (hsn : StrongNormalizable t)
    (hhead : CandidateHead A t) :
    Candidate A t := by
  exact Candidate.mk A t hsn hhead

theorem candidate_of_betaStrong {A t : Term}
    (hstrong : BetaStrong t)
    (hhead : CandidateHead A t) :
    Candidate A t := by
  exact candidate_with_betaStrong (betaStrong_implies_sn hstrong) hhead

theorem sort_candidate_from_betaStrong :
    Candidate Term.sort Term.sort := by
  exact candidate_of_betaStrong sort_betaStrong sort_candidateHead

theorem var_candidate_from_betaStrong (A : Term) (i : Idx) :
    Candidate A (Term.var i) := by
  exact candidate_of_betaStrong (var_betaStrong i) (var_candidateHead A i)

end BEDC.MetaCIC
