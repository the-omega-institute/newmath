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

theorem TokUnique_replacement
    {s : BaseReflectionSetup} {P : s.Pi} (tok : TokUnique s P)
    {x y : s.SigObj} {p : s.Pkg} :
    s.TokIntro P x p -> s.TokIntro P y p -> s.hsame x y := by
  intro left right
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

def PolicyTokenMode (s : BaseReflectionSetup) (P : s.Pi) : Prop := TokUnique s P

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

inductive PsameBase (s : BaseReflectionSetup) (P : s.Pi) : s.Pkg → s.Pkg → Prop where
  | intro {x y : s.SigObj} {p q : s.Pkg} :
      s.TokIntro P x p → s.TokIntro P y q → s.hsame x y → PsameBase s P p q

theorem PsameBase_constructor
    {s : BaseReflectionSetup} {P : s.Pi} {x y : s.SigObj} {p q : s.Pkg} :
    s.TokIntro P x p → s.TokIntro P y q → s.hsame x y → PsameBase s P p q := by
  intro left right same
  exact PsameBase.intro left right same

theorem PsameBase_inversion_exists
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q ->
      exists x : s.SigObj, exists y : s.SigObj,
        s.TokIntro P x p /\ s.TokIntro P y q /\ s.hsame x y := by
  intro base
  cases base with
  | intro left right same =>
      exact Exists.intro _ (Exists.intro _ (And.intro left (And.intro right same)))

abbrev PsameSig (s : BaseReflectionSetup) (P : s.Pi) : s.Pkg → s.Pkg → Prop := PsameBase s P

inductive PsameEqClosure (s : BaseReflectionSetup) (P : s.Pi) : s.Pkg → s.Pkg → Prop where
  | refl {p : s.Pkg} : PsameEqClosure s P p p
  | base {p q : s.Pkg} : PsameBase s P p q → PsameEqClosure s P p q
  | symm {p q : s.Pkg} : PsameEqClosure s P p q → PsameEqClosure s P q p
  | trans {p q r : s.Pkg} :
      PsameEqClosure s P p q → PsameEqClosure s P q r → PsameEqClosure s P p r

theorem PsameEqClosure_base_inclusion
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q -> PsameEqClosure s P p q := by
  intro base
  exact PsameEqClosure.base base

theorem PsameEqClosure_base_intro {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q → PsameEqClosure s P p q := by
  intro base
  exact PsameEqClosure.base base

def ClosureReflect (s : BaseReflectionSetup) (P : s.Pi) : Prop :=
  ∀ {x y : s.SigObj} {p q : s.Pkg},
    s.TokIntro P x p → s.TokIntro P y q → PsameEqClosure s P p q → s.hsame x y

structure PBaseData (s : BaseReflectionSetup) (P : s.Pi) (p q : s.Pkg) : Type where
  x : s.SigObj
  y : s.SigObj
  leftIntro : s.TokIntro P x p
  rightIntro : s.TokIntro P y q
  sigSame : s.hsame x y

theorem PBaseData_to_PsameBase {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PBaseData s P p q → PsameBase s P p q := by
  intro data
  cases data with
  | mk x y left right same =>
      exact PsameBase.intro left right same

theorem PBaseData_witnesses {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PBaseData s P p q ->
      exists x : s.SigObj, exists y : s.SigObj,
        s.TokIntro P x p /\ s.TokIntro P y q /\ s.hsame x y := by
  intro data
  cases data with
  | mk x y left right same =>
      exact Exists.intro x (Exists.intro y (And.intro left (And.intro right same)))

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

theorem PsameBase_iff_PBaseData {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q ↔ Nonempty (PBaseData s P p q) := by
  exact Iff.intro
    (fun base => PsameBase_inversion base)
    (fun data =>
      match data with
      | Nonempty.intro d => PBaseData_to_PsameBase d)

theorem PsameBase_witnesses_from_base {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q -> exists x : s.SigObj, exists y : s.SigObj,
      s.TokIntro P x p /\ s.TokIntro P y q /\ s.hsame x y := by
  intro base
  cases base with
  | intro left right same =>
      exact Exists.intro _ (Exists.intro _ (And.intro left (And.intro right same)))

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

theorem BaseReflection_active
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {x y : s.SigObj} {p q : s.Pkg}
    (left : s.TokIntro P x p) (right : s.TokIntro P y q)
    (base : PsameBase s P p q) : s.hsame x y := by
  exact PackageReflection_base eqv tok left right base

theorem PackageReflection_base_from_canonical
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (mode : CanonicalTokenMode s P)
    {x y : s.SigObj} {p q : s.Pkg}
    (left : s.TokIntro P x p) (right : s.TokIntro P y q)
    (base : PsameBase s P p q) : s.hsame x y := by
  exact PackageReflection_base eqv (CanonicalTokenMode_implies_TokUnique mode) left right base

theorem StableReflectionContract_from_canonical
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (mode : CanonicalTokenMode s P)
    {x y : s.SigObj} {p q : s.Pkg}
    (left : s.TokIntro P x p) (right : s.TokIntro P y q)
    (base : PsameBase s P p q) : s.hsame x y := by
  exact PackageReflection_base_from_canonical eqv mode left right base

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

theorem PsameBase_trans_under_tok_unique
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {p q r : s.Pkg} :
    PsameBase s P p q → PsameBase s P q r → PsameBase s P p r := by
  intro leftBase rightBase
  cases leftBase with
  | intro leftTok middleTokLeft leftSame =>
      cases rightBase with
      | intro middleTokRight rightTok rightSame =>
          have middleSame := tok.tokenReplacement middleTokLeft middleTokRight
          exact PsameBase.intro leftTok rightTok
            (eqv.trans leftSame (eqv.trans middleSame rightSame))

theorem PsameBase_equivalence_under_tok_unique
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    (introOf : forall p : s.Pkg, Nonempty (Subtype (fun x : s.SigObj => s.TokIntro P x p))) :
    (forall p : s.Pkg, PsameBase s P p p) /\
    (forall {p q : s.Pkg}, PsameBase s P p q -> PsameBase s P q p) /\
    (forall {p q r : s.Pkg}, PsameBase s P p q -> PsameBase s P q r -> PsameBase s P p r) := by
  constructor
  case left =>
    intro p
    cases introOf p with
    | intro witness =>
        exact PsameBase.intro witness.property witness.property (eqv.refl witness.val)
  case right =>
    constructor
    case left =>
      intro p q base
      cases base with
      | intro left right same =>
          exact PsameBase.intro right left (eqv.symm same)
    case right =>
      intro p q r leftBase rightBase
      exact PsameBase_trans_under_tok_unique eqv tok leftBase rightBase

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

theorem ClosureReflect_from_eqClosure
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    (introOf : forall p : s.Pkg, Nonempty (Subtype (fun x : s.SigObj => s.TokIntro P x p))) :
    ClosureReflect s P := by
  intro x y p q left right closure
  exact PackageReflection_eqClosure eqv tok introOf left right closure

theorem ClosureReflect_from_canonical
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (mode : CanonicalTokenMode s P)
    (introOf : forall p : s.Pkg, Nonempty (Subtype (fun x : s.SigObj => s.TokIntro P x p))) :
    ClosureReflect s P := by
  exact ClosureReflect_from_eqClosure eqv (CanonicalTokenMode_implies_TokUnique mode) introOf

theorem eqClosure_export_requires_closure_reflect
    {s : BaseReflectionSetup} {P : s.Pi} (reflect : ClosureReflect s P)
    {x y : s.SigObj} {p q : s.Pkg} :
    s.TokIntro P x p -> s.TokIntro P y q -> PsameEqClosure s P p q -> s.hsame x y := by
  intro left right closure
  exact reflect left right closure

theorem StableReflectionContract
    {s : BaseReflectionSetup} {P : s.Pi} (eqv : HSameEquiv s) :
    ((tok : PolicyTokenMode s P) ->
      forall {x y : s.SigObj} {p q : s.Pkg},
        s.TokIntro P x p -> s.TokIntro P y q -> PsameBase s P p q -> s.hsame x y) /\
    ((mode : CanonicalTokenMode s P) ->
      forall {x y : s.SigObj} {p q : s.Pkg},
        s.TokIntro P x p -> s.TokIntro P y q -> PsameBase s P p q -> s.hsame x y) := by
  constructor
  intro tok x y p q left right base
  exact PackageReflection_base eqv tok left right base
  intro mode x y p q left right base
  exact PackageReflection_base eqv (CanonicalTokenMode_implies_TokUnique mode) left right base

structure GeneratedSameSig (s : BaseReflectionSetup) (P : s.Pi) (h k : s.Hist) : Type where
  leftSigObj : s.SigObj
  rightSigObj : s.SigObj
  leftEvidence : s.Evidence
  rightEvidence : s.Evidence
  leftSig : s.SigGen P h leftSigObj leftEvidence
  rightSig : s.SigGen P k rightSigObj rightEvidence
  sigSame : s.hsame leftSigObj rightSigObj

theorem GeneratedSameSig_hsame
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (gen : GeneratedSameSig s P h k) :
    s.hsame gen.leftSigObj gen.rightSigObj := by
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact sigSame

def GeneratedSameSig_symm
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (eqv : HSameEquiv s) :
    GeneratedSameSig s P h k -> GeneratedSameSig s P k h := by
  intro gen
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact {
        leftSigObj := rightSigObj
        rightSigObj := leftSigObj
        leftEvidence := rightEvidence
        rightEvidence := leftEvidence
        leftSig := rightSig
        rightSig := leftSig
        sigSame := eqv.symm sigSame
      }

theorem GeneratedSameSig_symm_nonempty
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (eqv : HSameEquiv s) :
    Nonempty (GeneratedSameSig s P h k) → Nonempty (GeneratedSameSig s P k h) := by
  intro hgen
  cases hgen with
  | intro gen =>
      cases gen with
      | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
          exact Nonempty.intro {
            leftSigObj := rightSigObj
            rightSigObj := leftSigObj
            leftEvidence := rightEvidence
            rightEvidence := leftEvidence
            leftSig := rightSig
            rightSig := leftSig
            sigSame := eqv.symm sigSame
          }

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

theorem ClosureReflect_to_GeneratedSameSig
    {s : BaseReflectionSetup} {P : s.Pi}
    (reflect : ClosureReflect s P)
    {h k : s.Hist} {x y : s.SigObj} {p q : s.Pkg}
    {evL evR : s.Evidence}
    (leftSig : s.SigGen P h x evL)
    (rightSig : s.SigGen P k y evR)
    (leftTok : s.TokIntro P x p)
    (rightTok : s.TokIntro P y q)
    (closure : PsameEqClosure s P p q) :
    Nonempty (GeneratedSameSig s P h k) := by
  exact Nonempty.intro {
    leftSigObj := x
    rightSigObj := y
    leftEvidence := evL
    rightEvidence := evR
    leftSig := leftSig
    rightSig := rightSig
    sigSame := reflect leftTok rightTok closure
  }

structure ExactGlobalizeBase (s : BaseReflectionSetup) (P : s.Pi) (D : s.Domain) : Prop where
  coverage : ∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h
  soundness : ∀ h k p q,
    s.InGapSig P D p h → s.InGapSig P D q k →
    GeneratedSameSig s P h k → PsameBase s P p q
  completeness : ∀ h k p q,
    s.InGapSig P D p h → s.InGapSig P D q k →
    PsameBase s P p q → Nonempty (GeneratedSameSig s P h k)

theorem ExactGlobalizeBase_soundness_exports_base
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
    GeneratedSameSig s P h k → PsameBase s P p q := by
  intro hp hq gen
  exact ex.soundness h k p q hp hq gen

theorem ExactGlobalizeBase_completeness
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
    PsameBase s P p q → Nonempty (GeneratedSameSig s P h k) := by
  intro hp hq base
  exact ex.completeness h k p q hp hq base

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

theorem ExactGlobalizeBase_coverage
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) : ∀ h, s.InDom D h → ∃ p, s.InGapSig P D p h := by
  exact ex.coverage

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

theorem ExactGlobalizeBase_classify_iff_from_directions
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (soundness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      GeneratedSameSig s P h k → PsameBase s P p q)
    (completeness : ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      PsameBase s P p q → Nonempty (GeneratedSameSig s P h k))
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k) := by
  constructor
  case mp =>
    intro hbase
    exact completeness h k p q hp hq hbase
  case mpr =>
    intro hgen
    cases hgen with
    | intro hsig =>
        exact soundness h k p q hp hq hsig

theorem ExactGlobalizeBase_exports_base_relation
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ∀ {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_no_closure_export
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ∀ {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_relation_is_base
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ∀ {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

def NotExported (s : BaseReflectionSetup) (P : s.Pi) (D : s.Domain)
    (_ex : ExactGlobalizeBase s P D) : Prop :=
  forall {h k : s.Hist} {p q : s.Pkg},
    s.InGapSig P D p h -> s.InGapSig P D q k ->
      (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))

theorem ClosureReflect_preserves_base_export
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) (_closure : ClosureReflect s P) :
    ∀ {h k : s.Hist} {p q : s.Pkg},
      s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_exact
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))) := by
  exact And.intro ex.coverage (by
    intro h k p q hp hq
    exact ExactGlobalizeBase_classify_iff ex hp hq)

end BEDC.BaseReflection
