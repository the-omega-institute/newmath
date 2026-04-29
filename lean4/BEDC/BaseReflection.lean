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

inductive PsameBase (s : BaseReflectionSetup) (P : s.Pi) : s.Pkg → s.Pkg → Prop where
  | intro {x y : s.SigObj} {p q : s.Pkg} :
      s.TokIntro P x p → s.TokIntro P y q → s.hsame x y → PsameBase s P p q

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

structure GeneratedSameSig (s : BaseReflectionSetup) (P : s.Pi) (h k : s.Hist) : Type where
  leftSigObj : s.SigObj
  rightSigObj : s.SigObj
  leftEvidence : s.Evidence
  rightEvidence : s.Evidence
  leftSig : s.SigGen P h leftSigObj leftEvidence
  rightSig : s.SigGen P k rightSigObj rightEvidence
  sigSame : s.hsame leftSigObj rightSigObj

structure ExactGlobalizeBase (s : BaseReflectionSetup) (P : s.Pi) (D : s.Domain) : Prop where
  coverage : ∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h
  soundness : ∀ h k p q,
    s.InGapSig P D p h → s.InGapSig P D q k →
    GeneratedSameSig s P h k → PsameBase s P p q
  completeness : ∀ h k p q,
    s.InGapSig P D p h → s.InGapSig P D q k →
    PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)

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
