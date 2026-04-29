/-! BEDC base-reflection scaffold. -/

namespace BEDC.BaseReflection

structure BaseReflectionSetup where
  Hist : Type
  SigObj : Type
  Pkg : Type
  Pi : Type
  Domain : Type
  Evidence : Type
  hsame : SigObj → SigObj → Prop
  InDom : Domain → Hist → Prop
  SigGen : Pi → Hist → SigObj → Evidence → Prop
  TokIntro : Pi → SigObj → Pkg → Prop
  InGapSig : Pi → Domain → Pkg → Hist → Prop

structure HSameEquiv (s : BaseReflectionSetup) : Prop where
  refl  : ∀ x, s.hsame x x
  symm  : ∀ {x y}, s.hsame x y → s.hsame y x
  trans : ∀ {x y z}, s.hsame x y → s.hsame y z → s.hsame x z

structure TokUnique (s : BaseReflectionSetup) (P : s.Pi) : Prop where
  tokenReplacement : ∀ {x y p},
    s.TokIntro P x p → s.TokIntro P y p → s.hsame x y

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

inductive PsameBase (s : BaseReflectionSetup) (P : s.Pi) : s.Pkg → s.Pkg → Prop where
  | intro {x y : s.SigObj} {p q : s.Pkg} :
      s.TokIntro P x p → s.TokIntro P y q → s.hsame x y → PsameBase s P p q

theorem PsameBase_constructor
    {s : BaseReflectionSetup} {P : s.Pi} {x y : s.SigObj} {p q : s.Pkg} :
    s.TokIntro P x p → s.TokIntro P y q → s.hsame x y → PsameBase s P p q := by
  intro left right same
  exact PsameBase.intro left right same

abbrev PsameSig (s : BaseReflectionSetup) (P : s.Pi) : s.Pkg → s.Pkg → Prop := PsameBase s P

inductive PsameEqClosure (s : BaseReflectionSetup) (P : s.Pi) : s.Pkg → s.Pkg → Prop where
  | refl {p : s.Pkg} : PsameEqClosure s P p p
  | base {p q : s.Pkg} : PsameBase s P p q → PsameEqClosure s P p q
  | symm {p q : s.Pkg} : PsameEqClosure s P p q → PsameEqClosure s P q p
  | trans {p q r : s.Pkg} :
      PsameEqClosure s P p q → PsameEqClosure s P q r → PsameEqClosure s P p r

def ClosureReflect (s : BaseReflectionSetup) (P : s.Pi) : Prop :=
  ∀ {x y : s.SigObj} {p q : s.Pkg},
    s.TokIntro P x p → s.TokIntro P y q → PsameEqClosure s P p q → s.hsame x y

structure PBaseData (s : BaseReflectionSetup) (P : s.Pi) (p q : s.Pkg) : Type where
  x : s.SigObj
  y : s.SigObj
  leftIntro : s.TokIntro P x p
  rightIntro : s.TokIntro P y q
  sigSame : s.hsame x y

theorem PsameBase_inversion {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q → Nonempty (PBaseData s P p q) := by
  intro h
  cases h with
  | intro left right same =>
      exact Nonempty.intro {
        x := _
        y := _
        leftIntro := left
        rightIntro := right
        sigSame := same
      }

theorem PackageReflection_base
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {x y : s.SigObj} {p q : s.Pkg}
    (left : s.TokIntro P x p) (right : s.TokIntro P y q)
    (base : PsameBase s P p q) : s.hsame x y := by
  cases base with
  | intro left0 right0 same0 =>
      have x_to_x0 := tok.tokenReplacement left left0
      have y_to_y0 := tok.tokenReplacement right right0
      exact eqv.trans (eqv.trans x_to_x0 same0) (eqv.symm y_to_y0)

theorem PackageReflection_token_unique
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {x y : s.SigObj} {p q : s.Pkg}
    (left : s.TokIntro P x p) (right : s.TokIntro P y q)
    (base : PsameBase s P p q) : s.hsame x y := by
  exact PackageReflection_base eqv tok left right base

theorem PsameBase_iff_hsame_under_tok_unique
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {x y : s.SigObj} {p q : s.Pkg}
    (left : s.TokIntro P x p) (right : s.TokIntro P y q) :
    PsameBase s P p q ↔ s.hsame x y := by
  constructor
  case mp =>
    intro base
    exact PackageReflection_base eqv tok left right base
  case mpr =>
    intro same
    exact PsameBase.intro left right same

theorem PackageReflection_eqClosure
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    (introOf : forall p : s.Pkg, Nonempty (Subtype (fun x : s.SigObj => s.TokIntro P x p)))
    {x y : s.SigObj} {p q : s.Pkg}
    (left : s.TokIntro P x p) (right : s.TokIntro P y q)
    (closure : PsameEqClosure s P p q) : s.hsame x y := by
  induction closure generalizing x y with
  | refl =>
      exact tok.tokenReplacement left right
  | base base =>
      exact PackageReflection_base eqv tok left right base
  | symm closure ih =>
      exact eqv.symm (ih right left)
  | trans leftClosure rightClosure leftIH rightIH =>
      cases introOf _ with
      | intro middle =>
          exact eqv.trans (leftIH left middle.property) (rightIH middle.property right)

structure GeneratedSameSig (s : BaseReflectionSetup) (P : s.Pi) (h k : s.Hist) : Type where
  leftSigObj : s.SigObj
  rightSigObj : s.SigObj
  leftEvidence : s.Evidence
  rightEvidence : s.Evidence
  leftSig : s.SigGen P h leftSigObj leftEvidence
  rightSig : s.SigGen P k rightSigObj rightEvidence
  sigSame : s.hsame leftSigObj rightSigObj

theorem GeneratedSameSig_psameBase
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist} {p q : s.Pkg}
    (gen : GeneratedSameSig s P h k)
    (left : s.TokIntro P gen.leftSigObj p)
    (right : s.TokIntro P gen.rightSigObj q) : PsameBase s P p q := by
  exact PsameBase.intro left right gen.sigSame

theorem PsameBase_to_GeneratedSameSig_under_tok_unique
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {h k : s.Hist} {x y : s.SigObj} {p q : s.Pkg}
    {leftEvidence rightEvidence : s.Evidence}
    (leftSig : s.SigGen P h x leftEvidence)
    (rightSig : s.SigGen P k y rightEvidence)
    (leftTok : s.TokIntro P x p)
    (rightTok : s.TokIntro P y q)
    (base : PsameBase s P p q) : Nonempty (GeneratedSameSig s P h k) := by
  exact Nonempty.intro {
    leftSigObj := x
    rightSigObj := y
    leftEvidence := leftEvidence
    rightEvidence := rightEvidence
    leftSig := leftSig
    rightSig := rightSig
    sigSame := PackageReflection_base eqv tok leftTok rightTok base
  }

structure ExactGlobalizeBase (s : BaseReflectionSetup) (P : s.Pi) (D : s.Domain) : Prop where
  coverage : ∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h
  soundness : ∀ h k p q,
    s.InGapSig P D p h → s.InGapSig P D q k →
    GeneratedSameSig s P h k → PsameBase s P p q
  completeness : ∀ h k p q,
    s.InGapSig P D p h → s.InGapSig P D q k →
    PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)

theorem ExactGlobalizeBase_from_fields
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (coverage : ∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h)
    (soundness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      GeneratedSameSig s P h k → PsameBase s P p q)
    (completeness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)) :
    ExactGlobalizeBase s P D := by
  exact {
    coverage := coverage
    soundness := soundness
    completeness := completeness
  }

theorem ExactGlobalizeBase_classify_iff
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k) := by
  constructor
  case mp =>
    intro hbase
    exact ex.completeness h k p q hp hq hbase
  case mpr =>
    intro hgen
    cases hgen with
    | intro hsig =>
        exact ex.soundness h k p q hp hq hsig

end BEDC.BaseReflection
