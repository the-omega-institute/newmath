import BEDC.MetaCIC.Normalization.ClosedSN
import BEDC.MetaCIC.SubjectReduction.ClosedDischarge
import BEDC.MetaCIC.SubjectReduction.ClosedBinderDischarge
import BEDC.MetaCIC.Typing
import BEDC.MetaCIC.ClosedTerm

namespace BEDC.MetaCIC

def falseEncoding : Term :=
  Term.pi Term.sort (Term.var 0)

def ClosedProofOfFalse (t : Term) : Prop :=
  HasType [] t falseEncoding ∧ ClosedAt 0 t

def no_closed_proof_of_false : Prop :=
  ¬ ∃ (t : Term), ClosedProofOfFalse t

def NoClosedProofOfFalseStatement : Prop :=
  no_closed_proof_of_false

def ClosedNormalProofOfFalse (t : Term) : Prop :=
  ClosedProofOfFalse t ∧ BetaStrong t

def NoClosedNormalProofOfFalseStatement : Prop :=
  ¬ ∃ (t : Term), ClosedNormalProofOfFalse t

def ClosedNormalConsistencyAssemblyStatement : Prop :=
  ∀ {t : Term}, HasType [] t falseEncoding → ClosedAt 0 t → BetaStrong t → False

def ClosedReductionConsistencyAssemblyStatement : Prop :=
  NoClosedProofOfFalseStatement

theorem falseEncoding_closed_at_zero :
    ClosedAt 0 falseEncoding := by
  unfold falseEncoding
  apply ClosedAt.piClosed
  · exact ClosedAt.sortClosed
  · apply ClosedAt.varClosed
    exact Nat.zero_lt_succ 0

theorem falseEncoding_has_type_sort :
    HasType [] falseEncoding Term.sort := by
  unfold falseEncoding
  apply HasType.piRule
  · exact HasType.sortRule []
  · apply HasType.varRule
    rfl

theorem betaStrong_app_head {f a : Term}
    (h : BetaStrong (Term.app f a)) :
    BetaStrong f := by
  intro hstep
  cases hstep with
  | intro f' hf' =>
      apply h
      exact Exists.intro (Term.app f' a)
        (BetaStep.congApp1 f f' a hf')

theorem betaStrong_app_arg {f a : Term}
    (h : BetaStrong (Term.app f a)) :
    BetaStrong a := by
  intro hstep
  cases hstep with
  | intro a' ha' =>
      apply h
      exact Exists.intro (Term.app f a')
        (BetaStep.congApp2 f a a' ha')

theorem betaStrong_lam_dom {dom body : Term}
    (h : BetaStrong (Term.lam dom body)) :
    BetaStrong dom := by
  intro hstep
  cases hstep with
  | intro dom' hdom' =>
      apply h
      exact Exists.intro (Term.lam dom' body)
        (BetaStep.congLamDom dom dom' body hdom')

theorem betaStrong_lam_body {dom body : Term}
    (h : BetaStrong (Term.lam dom body)) :
    BetaStrong body := by
  intro hstep
  cases hstep with
  | intro body' hbody' =>
      apply h
      exact Exists.intro (Term.lam dom body')
        (BetaStep.congLam dom body body' hbody')

theorem betaStrong_pi_dom {dom cod : Term}
    (h : BetaStrong (Term.pi dom cod)) :
    BetaStrong dom := by
  intro hstep
  cases hstep with
  | intro dom' hdom' =>
      apply h
      exact Exists.intro (Term.pi dom' cod)
        (BetaStep.congPiDom dom dom' cod hdom')

theorem betaStrong_pi_cod {dom cod : Term}
    (h : BetaStrong (Term.pi dom cod)) :
    BetaStrong cod := by
  intro hstep
  cases hstep with
  | intro cod' hcod' =>
      apply h
      exact Exists.intro (Term.pi dom cod')
        (BetaStep.congPiCod dom cod cod' hcod')

theorem betaStrong_app_not_lam_head {dom body arg : Term}
    (h : BetaStrong (Term.app (Term.lam dom body) arg)) :
    False := by
  apply h
  exact Exists.intro (substitute 0 arg body)
    (BetaStep.beta dom body arg)

theorem lookup_empty_absurd_some {i : Idx} {A : Term} :
    Ctx.lookup [] i = some A → False := by
  intro h
  cases h

theorem lookup_sort_ctx_not_var_zero {i : Idx} :
    Ctx.lookup [Term.sort] i = some (Term.var 0) → False := by
  cases i with
  | zero =>
      intro h
      cases h
  | succ i =>
      intro h
      cases h

theorem lookup_sort_ctx_not_pi {i : Idx} {dom cod : Term} :
    Ctx.lookup [Term.sort] i = some (Term.pi dom cod) → False := by
  cases i with
  | zero =>
      intro h
      cases h
  | succ i =>
      intro h
      cases h

theorem empty_ctx_sort_not_pi {dom cod : Term}
    (h : HasType [] Term.sort (Term.pi dom cod)) :
    False := by
  cases h

theorem sort_ctx_sort_not_var_zero
    (h : HasType [Term.sort] Term.sort (Term.var 0)) :
    False := by
  cases h

theorem empty_ctx_pi_not_pi_type {d c dom cod : Term}
    (h : HasType [] (Term.pi d c) (Term.pi dom cod)) :
    False := by
  cases h

theorem sort_ctx_pi_not_var_zero {d c : Term}
    (h : HasType [Term.sort] (Term.pi d c) (Term.var 0)) :
    False := by
  cases h

theorem sort_ctx_lam_not_var_zero {d b : Term}
    (h : HasType [Term.sort] (Term.lam d b) (Term.var 0)) :
    False := by
  cases h

theorem sort_ctx_var_not_var_zero {i : Idx}
    (h : HasType [Term.sort] (Term.var i) (Term.var 0)) :
    False := by
  cases h with
  | varRule Γ j A hlookup =>
      exact lookup_sort_ctx_not_var_zero hlookup

theorem empty_ctx_var_not_pi {i : Idx} {dom cod : Term}
    (h : HasType [] (Term.var i) (Term.pi dom cod)) :
    False := by
  cases h with
  | varRule Γ j A hlookup =>
      exact lookup_empty_absurd_some hlookup

theorem sort_ctx_var_not_pi {i : Idx} {dom cod : Term}
    (h : HasType [Term.sort] (Term.var i) (Term.pi dom cod)) :
    False := by
  cases h with
  | varRule Γ j A hlookup =>
      exact lookup_sort_ctx_not_pi hlookup

theorem app_betaStrong_empty_head_not_pi :
    ∀ {f a dom cod : Term},
      ClosedAt 0 f →
      BetaStrong (Term.app f a) →
      HasType [] f (Term.pi dom cod) →
      False := by
  intro f a dom cod hclosed
  generalize hn : (0 : Idx) = n at hclosed
  induction hclosed generalizing a dom cod with
  | varClosed hlt =>
      cases hn
      intro _ _
      exact Nat.not_lt_zero _ hlt
  | appClosed hfclosed haclosed ihf _iha =>
      cases hn
      intro hnormal htype
      cases hasType_app_empty_ctx_pi htype with
      | intro appDom rest =>
        cases rest with
        | intro appCod happ =>
          exact ihf
            (dom := appDom)
            (cod := appCod)
            rfl
            (betaStrong_app_head hnormal)
            happ.left
  | lamClosed hdom hbody _ihdom _ihbody =>
      cases hn
      intro hnormal _htype
      exact betaStrong_app_not_lam_head hnormal
  | piClosed hdom hcod _ihdom _ihcod =>
      cases hn
      intro _hnormal htype
      exact empty_ctx_pi_not_pi_type htype
  | sortClosed =>
      cases hn
      intro _hnormal htype
      exact empty_ctx_sort_not_pi htype

theorem app_betaStrong_empty_not_typed :
    ∀ {f a A : Term},
      ClosedAt 0 (Term.app f a) →
      BetaStrong (Term.app f a) →
      HasType [] (Term.app f a) A →
      False := by
  intro f a A hclosed hnormal htype
  cases hclosed with
  | appClosed hfclosed haclosed =>
      cases htype with
      | appRule Γ f0 a0 dom cod hf ha =>
          exact app_betaStrong_empty_head_not_pi
            hfclosed
            hnormal
            hf

theorem app_betaStrong_sort_ctx_head_not_pi :
    ∀ {f a dom cod : Term},
      ClosedAt 1 f →
      BetaStrong (Term.app f a) →
      HasType [Term.sort] f (Term.pi dom cod) →
      False := by
  intro f a dom cod hclosed
  generalize hn : (1 : Idx) = n at hclosed
  induction hclosed generalizing a dom cod with
  | varClosed hlt =>
      cases hn
      intro _hnormal htype
      exact sort_ctx_var_not_pi htype
  | appClosed hfclosed haclosed ihf _iha =>
      cases hn
      intro hnormal htype
      cases hasType_app_ctx_components htype with
      | intro appDom rest =>
        cases rest with
        | intro appCod hcomponents =>
          exact ihf
            (dom := appDom)
            (cod := appCod)
            rfl
            (betaStrong_app_head hnormal)
            hcomponents.right.left
  | lamClosed hdom hbody _ihdom _ihbody =>
      cases hn
      intro hnormal _htype
      exact betaStrong_app_not_lam_head hnormal
  | piClosed hdom hcod _ihdom _ihcod =>
      cases hn
      intro _hnormal htype
      cases htype
  | sortClosed =>
      cases hn
      intro _hnormal htype
      cases htype

theorem app_betaStrong_sort_ctx_not_typed :
    ∀ {f a A : Term},
      ClosedAt 1 (Term.app f a) →
      BetaStrong (Term.app f a) →
      HasType [Term.sort] (Term.app f a) A →
      False := by
  intro f a A hclosed hnormal htype
  cases hclosed with
  | appClosed hfclosed haclosed =>
      cases htype with
      | appRule Γ f0 a0 dom cod hf ha =>
          exact app_betaStrong_sort_ctx_head_not_pi
            hfclosed
            hnormal
            hf

theorem sort_ctx_closed_betaStrong_not_var_zero :
    ∀ {t : Term},
      ClosedAt 1 t →
      BetaStrong t →
      HasType [Term.sort] t (Term.var 0) →
      False := by
  intro t hclosed
  generalize hn : (1 : Idx) = n at hclosed
  induction hclosed with
  | varClosed hlt =>
      cases hn
      intro _hnormal htype
      exact sort_ctx_var_not_var_zero htype
  | appClosed hfclosed haclosed ihf iha =>
      cases hn
      intro hnormal htype
      exact app_betaStrong_sort_ctx_not_typed
        (ClosedAt.appClosed hfclosed haclosed)
        hnormal
        htype
  | lamClosed hdom hbody ihdom ihbody =>
      cases hn
      intro _hnormal htype
      exact sort_ctx_lam_not_var_zero htype
  | piClosed hdom hcod ihdom ihcod =>
      cases hn
      intro _hnormal htype
      exact sort_ctx_pi_not_var_zero htype
  | sortClosed =>
      cases hn
      intro _hnormal htype
      exact sort_ctx_sort_not_var_zero htype

theorem closed_betaStrong_false_absurd :
    ∀ {t : Term},
      HasType [] t falseEncoding →
      ClosedAt 0 t →
      BetaStrong t →
      False := by
  intro t htype hclosed hnormal
  cases hclosed with
  | varClosed hlt =>
      exact Nat.not_lt_zero _ hlt
  | appClosed hfclosed haclosed =>
      exact app_betaStrong_empty_not_typed
        (ClosedAt.appClosed hfclosed haclosed)
        hnormal
        htype
  | lamClosed hdom hbody =>
      cases hasType_lam_empty_ctx_pi htype with
      | intro cod hcomponents =>
          unfold falseEncoding at hcomponents
          cases hcomponents.left
          have hbodyType := hcomponents.right.right
          rw [shift_closed 0 Term.sort ClosedAt.sortClosed] at hbodyType
          exact sort_ctx_closed_betaStrong_not_var_zero
            hbody
            (betaStrong_lam_body hnormal)
            hbodyType
  | piClosed hdom hcod =>
      unfold falseEncoding at htype
      cases htype
  | sortClosed =>
      unfold falseEncoding at htype
      cases htype

theorem no_closed_normal_proof_of_false :
    NoClosedNormalProofOfFalseStatement := by
  intro h
  cases h with
  | intro t hproof =>
      exact closed_betaStrong_false_absurd
        hproof.left.left
        hproof.left.right
        hproof.right

theorem closed_normal_consistency_assembly :
    ClosedNormalConsistencyAssemblyStatement := by
  intro t htype hclosed hnormal
  exact closed_betaStrong_false_absurd htype hclosed hnormal

def closed_consistency_reduction_obstruction : Prop :=
  SubjectReductionClosedStatement

theorem closed_consistency_reduction_obstruction_not_available :
    ¬ closed_consistency_reduction_obstruction := by
  unfold closed_consistency_reduction_obstruction
  exact not_subject_reduction_closed

end BEDC.MetaCIC
