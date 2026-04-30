import BEDC.BaseReflection.Core

namespace BEDC.BaseReflection

structure TokUnique (s : BaseReflectionSetup) (P : s.Pi) : Prop where
  tokenReplacement : ∀ {x y p},
    s.TokIntro P x p → s.TokIntro P y p → s.hsame x y

theorem TokUnique_intro {s : BaseReflectionSetup} {P : s.Pi} :
    (forall {x y : s.SigObj} {p : s.Pkg},
      s.TokIntro P x p -> s.TokIntro P y p -> s.hsame x y) ->
    TokUnique s P := by
  intro h
  exact {
    tokenReplacement := by
      intro x y p left right
      exact h left right
  }

theorem TokUnique_iff_tokenReplacement {s : BaseReflectionSetup} {P : s.Pi} :
    TokUnique s P ↔
      (∀ {x y : s.SigObj} {p : s.Pkg},
        s.TokIntro P x p → s.TokIntro P y p → s.hsame x y) := by
  constructor
  case mp =>
    intro tok
    exact tok.tokenReplacement
  case mpr =>
    intro replacement
    exact {
      tokenReplacement := by
        intro x y p left right
        exact replacement left right
    }

theorem TokUnique_replacement
    {s : BaseReflectionSetup} {P : s.Pi} (tok : TokUnique s P)
    {x y : s.SigObj} {p : s.Pkg} :
    s.TokIntro P x p -> s.TokIntro P y p -> s.hsame x y := by
  intro left right
  exact tok.tokenReplacement left right

theorem token_replacement_base {s : BaseReflectionSetup} {P : s.Pi}
    (tok : TokUnique s P) {x y : s.SigObj} {p : s.Pkg} :
    s.TokIntro P x p -> s.TokIntro P y p -> s.hsame x y := by
  intro left right
  exact tok.tokenReplacement left right

theorem tok_unique_replacement_base {s : BaseReflectionSetup} {P : s.Pi}
    (tok : TokUnique s P) {x y : s.SigObj} {p : s.Pkg} :
    s.TokIntro P x p → s.TokIntro P y p → s.hsame x y := by
  intro left right
  exact tok.tokenReplacement left right

theorem TokUnique_replacement_from_pair {s : BaseReflectionSetup} {P : s.Pi}
    (tok : TokUnique s P) {x y : s.SigObj} {p : s.Pkg} :
    (s.TokIntro P x p ∧ s.TokIntro P y p) → s.hsame x y := by
  intro pair
  cases pair with
  | intro left right =>
      exact tok.tokenReplacement left right

theorem TokUnique_replacement_congr {s : BaseReflectionSetup} {P : s.Pi} (tok : TokUnique s P)
    {x y : s.SigObj} {p q : s.Pkg} :
    p = q → s.TokIntro P x p → s.TokIntro P y q → s.hsame x y := by
  intro same left right
  cases same
  exact tok.tokenReplacement left right

theorem TokUnique_replacement_self
    {s : BaseReflectionSetup} {P : s.Pi} (tok : TokUnique s P)
    {x : s.SigObj} {p : s.Pkg} : s.TokIntro P x p -> s.hsame x x := by
  intro introProof
  exact tok.tokenReplacement introProof introProof

theorem TokUnique_replacement_symm
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {x y : s.SigObj} {p : s.Pkg} :
    s.TokIntro P x p → s.TokIntro P y p → s.hsame y x := by
  intro left right
  exact eqv.symm (tok.tokenReplacement left right)

theorem TokUnique_replacement_pair
    {s : BaseReflectionSetup} {P : s.Pi} (eqv : HSameEquiv s) (tok : TokUnique s P)
    {x y : s.SigObj} {p : s.Pkg} :
    s.TokIntro P x p → s.TokIntro P y p → s.hsame x y ∧ s.hsame y x := by
  intro left right
  constructor
  · exact tok.tokenReplacement left right
  · exact eqv.symm (tok.tokenReplacement left right)

theorem TokUnique_replacement_trans
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {x y z : s.SigObj} {p q : s.Pkg} :
    s.TokIntro P x p -> s.TokIntro P y p ->
    s.TokIntro P y q -> s.TokIntro P z q -> s.hsame x z := by
  intro xp yp yq zq
  have xy : s.hsame x y := tok.tokenReplacement xp yp
  have yz : s.hsame y z := tok.tokenReplacement yq zq
  exact eqv.trans xy yz

def PolicyTokenMode (s : BaseReflectionSetup) (P : s.Pi) : Prop := TokUnique s P

theorem PolicyTokenMode_iff_TokUnique {s : BaseReflectionSetup} {P : s.Pi} :
    PolicyTokenMode s P <-> TokUnique s P := by
  exact Iff.intro
    (fun mode => mode)
    (fun tok => tok)

structure CanonicalTokenMode (s : BaseReflectionSetup) (P : s.Pi) : Type where
  TokCan : s.SigObj -> s.Pkg -> Prop
  introToCanonical : forall {x : s.SigObj} {p : s.Pkg}, s.TokIntro P x p -> TokCan x p
  canonicalUnique : forall {x y : s.SigObj} {p : s.Pkg}, TokCan x p -> TokCan y p -> s.hsame x y

theorem CanonicalTokenMode_implies_TokUnique
    {s : BaseReflectionSetup} {P : s.Pi}
    (mode : CanonicalTokenMode s P) : TokUnique s P := by
  exact {
    tokenReplacement := by
      intro x y p left right
      exact mode.canonicalUnique (mode.introToCanonical left) (mode.introToCanonical right)
  }

theorem CanonicalTokenMode_tokenReplacement {s : BaseReflectionSetup} {P : s.Pi}
    (mode : CanonicalTokenMode s P) {x y : s.SigObj} {p : s.Pkg} :
    s.TokIntro P x p -> s.TokIntro P y p -> s.hsame x y := by
  intro left right
  exact mode.canonicalUnique (mode.introToCanonical left) (mode.introToCanonical right)

theorem CanonicalTokenMode_replacement_and_unique {s : BaseReflectionSetup} {P : s.Pi}
    (mode : CanonicalTokenMode s P) :
    TokUnique s P ∧
      (∀ {x y : s.SigObj} {p : s.Pkg},
        s.TokIntro P x p → s.TokIntro P y p → s.hsame x y) := by
  constructor
  · exact CanonicalTokenMode_implies_TokUnique mode
  · intro x y p left right
    exact CanonicalTokenMode_tokenReplacement mode left right

end BEDC.BaseReflection
