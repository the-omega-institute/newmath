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

inductive PsameBase (s : BaseReflectionSetup) (P : s.Pi) : s.Pkg → s.Pkg → Prop where
  | intro {x y : s.SigObj} {p q : s.Pkg} :
      s.TokIntro P x p → s.TokIntro P y q → s.hsame x y → PsameBase s P p q

theorem PsameBase_constructor
    {s : BaseReflectionSetup} {P : s.Pi} {x y : s.SigObj} {p q : s.Pkg} :
    s.TokIntro P x p → s.TokIntro P y q → s.hsame x y → PsameBase s P p q := by
  intro left right same
  exact PsameBase.intro left right same

theorem PsameBase_symm_under_equiv {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) {p q : s.Pkg} :
    PsameBase s P p q → PsameBase s P q p := by
  intro base
  cases base with
  | intro left right same =>
      exact PsameBase.intro right left (eqv.symm same)

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

theorem PsameSig_iff_PsameBase {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameSig s P p q <-> PsameBase s P p q := by
  rfl

theorem PsameSig_constructor_inversion
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameSig s P p q ->
      exists x : s.SigObj, exists y : s.SigObj,
        s.TokIntro P x p /\ s.TokIntro P y q /\ s.hsame x y := by
  intro base
  cases base with
  | intro left right same =>
      exact Exists.intro _ (Exists.intro _ (And.intro left (And.intro right same)))

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

theorem PsameEqClosure_symm {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameEqClosure s P p q -> PsameEqClosure s P q p := by
  intro h
  exact PsameEqClosure.symm h

theorem PsameEqClosure_equivalence {s : BaseReflectionSetup} {P : s.Pi} :
    (forall p : s.Pkg, PsameEqClosure s P p p) /\
      (forall {p q : s.Pkg}, PsameEqClosure s P p q -> PsameEqClosure s P q p) /\
      (forall {p q r : s.Pkg},
        PsameEqClosure s P p q -> PsameEqClosure s P q r -> PsameEqClosure s P p r) := by
  exact And.intro
    (fun p => PsameEqClosure.refl)
    (And.intro
      (fun closure => PsameEqClosure.symm closure)
      (fun left right => PsameEqClosure.trans left right))

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

theorem active_token_mode_reflects_base
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (mode : PolicyTokenMode s P)
    {x y : s.SigObj} {p q : s.Pkg} :
    s.TokIntro P x p → s.TokIntro P y q → PsameBase s P p q → s.hsame x y := by
  intro left right base
  exact PackageReflection_base eqv mode left right base

theorem PackageReflection_base_from_data
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {x y : s.SigObj} {p q : s.Pkg}
    (left : s.TokIntro P x p) (right : s.TokIntro P y q)
    (data : PBaseData s P p q) : s.hsame x y := by
  cases data with
  | mk x0 y0 left0 right0 same0 =>
      exact eqv.trans (tok.tokenReplacement left left0)
        (eqv.trans same0 (eqv.symm (tok.tokenReplacement right right0)))

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

theorem exact_package_sameness
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    (introOf : forall p : s.Pkg, Nonempty (Subtype (fun x : s.SigObj => s.TokIntro P x p))) :
    (forall {x y : s.SigObj} {p q : s.Pkg},
      s.TokIntro P x p -> s.TokIntro P y q -> (PsameBase s P p q <-> s.hsame x y)) /\
    (forall p : s.Pkg, PsameBase s P p p) /\
    (forall {p q : s.Pkg}, PsameBase s P p q -> PsameBase s P q p) /\
    (forall {p q r : s.Pkg}, PsameBase s P p q -> PsameBase s P q r -> PsameBase s P p r) := by
  constructor
  case left =>
    intro x y p q left right
    exact PsameBase_iff_hsame_under_tok_unique eqv tok left right
  case right =>
    exact PsameBase_equivalence_under_tok_unique eqv tok introOf

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

theorem conditional_closure_reflection_schema
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    (introOf : forall p : s.Pkg, Nonempty (Subtype (fun x : s.SigObj => s.TokIntro P x p)))
    {x y : s.SigObj} {p q : s.Pkg} :
    s.TokIntro P x p -> s.TokIntro P y q -> PsameEqClosure s P p q -> s.hsame x y := by
  intro left right closure
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

def GeneratedSameSig_from_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist} {x y : s.SigObj}
    {ex ey : s.Evidence} :
    s.SigGen P h x ex -> s.SigGen P k y ey -> s.hsame x y ->
      GeneratedSameSig s P h k := by
  intro left right same
  exact {
    leftSigObj := x
    rightSigObj := y
    leftEvidence := ex
    rightEvidence := ey
    leftSig := left
    rightSig := right
    sigSame := same
  }

theorem GeneratedSameSig_hsame
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (gen : GeneratedSameSig s P h k) :
    s.hsame gen.leftSigObj gen.rightSigObj := by
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact sigSame

theorem GeneratedSameSig_left_witness
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (gen : GeneratedSameSig s P h k) :
    ∃ x : s.SigObj, ∃ e : s.Evidence, s.SigGen P h x e := by
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact Exists.intro leftSigObj (Exists.intro leftEvidence leftSig)

theorem GeneratedSameSig_right_witness
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (gen : GeneratedSameSig s P h k) :
    exists y : s.SigObj, exists e : s.Evidence, s.SigGen P k y e := by
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact Exists.intro rightSigObj (Exists.intro rightEvidence rightSig)

theorem GeneratedSameSig_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (gen : GeneratedSameSig s P h k) :
    ∃ x : s.SigObj, ∃ y : s.SigObj,
      ∃ leftEvidence : s.Evidence, ∃ rightEvidence : s.Evidence,
        s.SigGen P h x leftEvidence /\
        s.SigGen P k y rightEvidence /\ s.hsame x y := by
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact Exists.intro leftSigObj
        (Exists.intro rightSigObj
          (Exists.intro leftEvidence
            (Exists.intro rightEvidence
              (And.intro leftSig (And.intro rightSig sigSame)))))

theorem GeneratedSameSig_swap_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {h k : s.Hist}
    (eqv : HSameEquiv s) (gen : GeneratedSameSig s P h k) :
    exists y : s.SigObj, exists x : s.SigObj,
      exists rightEvidence : s.Evidence, exists leftEvidence : s.Evidence,
        s.SigGen P k y rightEvidence /\
        s.SigGen P h x leftEvidence /\ s.hsame y x := by
  cases gen with
  | mk leftSigObj rightSigObj leftEvidence rightEvidence leftSig rightSig sigSame =>
      exact Exists.intro rightSigObj
        (Exists.intro leftSigObj
          (Exists.intro rightEvidence
            (Exists.intro leftEvidence
              (And.intro rightSig (And.intro leftSig (eqv.symm sigSame))))))

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

theorem GeneratedSameSig_trans_nonempty_under_determinacy
    {s : BaseReflectionSetup} {P : s.Pi} (eqv : HSameEquiv s)
    (det : forall {h : s.Hist} {x y : s.SigObj} {ex ey : s.Evidence},
      s.SigGen P h x ex -> s.SigGen P h y ey -> s.hsame x y)
    {h k l : s.Hist} :
    Nonempty (GeneratedSameSig s P h k) ->
      Nonempty (GeneratedSameSig s P k l) ->
        Nonempty (GeneratedSameSig s P h l) := by
  intro left right
  cases left with
  | intro leftGen =>
      cases right with
      | intro rightGen =>
          cases leftGen with
          | mk leftSigObj midSigObj leftEvidence midEvidence leftSig midSig leftSame =>
              cases rightGen with
              | mk midSigObj' rightSigObj midEvidence' rightEvidence midSig' rightSig rightSame =>
                  exact Nonempty.intro {
                    leftSigObj := leftSigObj
                    rightSigObj := rightSigObj
                    leftEvidence := leftEvidence
                    rightEvidence := rightEvidence
                    leftSig := leftSig
                    rightSig := rightSig
                    sigSame := eqv.trans leftSame (eqv.trans (det midSig midSig') rightSame)
                  }

def GeneratedSameSig_trans_under_determinacy
    {s : BaseReflectionSetup} {P : s.Pi} (eqv : HSameEquiv s)
    (det : forall {h : s.Hist} {x y : s.SigObj} {ex ey : s.Evidence},
      s.SigGen P h x ex -> s.SigGen P h y ey -> s.hsame x y)
    {h k l : s.Hist} :
    GeneratedSameSig s P h k -> GeneratedSameSig s P k l -> GeneratedSameSig s P h l := by
  intro left right
  cases left with
  | mk leftSigObj midSigObj leftEvidence midEvidence leftSig midSig leftSame =>
      cases right with
      | mk midSigObj' rightSigObj midEvidence' rightEvidence midSig' rightSig rightSame =>
          exact {
            leftSigObj := leftSigObj
            rightSigObj := rightSigObj
            leftEvidence := leftEvidence
            rightEvidence := rightEvidence
            leftSig := leftSig
            rightSig := rightSig
            sigSame := eqv.trans leftSame (eqv.trans (det midSig midSig') rightSame)
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

theorem ExactGlobalizeBase_soundness
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ∀ h k p q,
      s.InGapSig P D p h → s.InGapSig P D q k →
      GeneratedSameSig s P h k → PsameBase s P p q := by
  exact ex.soundness

theorem ExactGlobalizeBase_soundness_exports_base
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
    GeneratedSameSig s P h k → PsameBase s P p q := by
  intro hp hq gen
  exact ex.soundness h k p q hp hq gen

theorem ExactGlobalizeBase_soundness_nonempty
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    Nonempty (GeneratedSameSig s P h k) -> PsameBase s P p q := by
  intro hgen
  cases hgen with
  | intro gen =>
      exact ex.soundness h k p q hp hq gen

theorem ExactGlobalizeBase_completeness
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
    PsameBase s P p q → Nonempty (GeneratedSameSig s P h k) := by
  intro hp hq base
  exact ex.completeness h k p q hp hq base

theorem ExactGlobalizeBase_sound_complete
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D)
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    (GeneratedSameSig s P h k -> PsameBase s P p q) /\
      (PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) := by
  constructor
  case left =>
    intro gen
    exact ex.soundness h k p q hp hq gen
  case right =>
    intro base
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

theorem ExactGlobalizeBase_coverage_sound_complete
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} (ex : ExactGlobalizeBase s P D) :
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        (GeneratedSameSig s P h k -> PsameBase s P p q) /\
          (PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k))) := by
  constructor
  case left =>
    exact ex.coverage
  case right =>
    intro h k p q hp hq
    constructor
    case left =>
      intro gen
      exact ex.soundness h k p q hp hq gen
    case right =>
      intro base
      exact ex.completeness h k p q hp hq base

theorem no_scaffold_laundering_coverage_soundness
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall h k p q,
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        GeneratedSameSig s P h k -> PsameBase s P p q) := by
  exact And.intro ex.coverage ex.soundness

theorem ExactGlobalizeBase_fields
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        GeneratedSameSig s P h k -> PsameBase s P p q) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) := by
  constructor
  case left =>
    exact ex.coverage
  case right =>
    constructor
    case left =>
      exact ex.soundness
    case right =>
      exact ex.completeness

theorem ExactGlobalizeBase_iff_fields {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} :
    ExactGlobalizeBase s P D <->
      ((forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
        (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
          GeneratedSameSig s P h k -> PsameBase s P p q) /\
        (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
          PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k))) := by
  constructor
  case mp =>
    intro ex
    exact ExactGlobalizeBase_fields ex
  case mpr =>
    intro fields
    cases fields with
    | intro coverage rest =>
        cases rest with
        | intro soundness completeness =>
            exact ExactGlobalizeBase_from_fields coverage soundness completeness

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

theorem no_scaffold_laundering_fields_and_classifier
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    ((forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        GeneratedSameSig s P h k -> PsameBase s P p q) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k))) /\
      (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))) := by
  exact And.intro
    (ExactGlobalizeBase_fields ex)
    (fun {h k : s.Hist} {p q : s.Pkg}
      (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) =>
        ExactGlobalizeBase_classify_iff ex hp hq)

theorem ExactGlobalizeBase_from_fields_classify_iff
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (coverage : forall h, s.InDom D h -> exists p, s.InGapSig P D p h)
    (soundness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      GeneratedSameSig s P h k -> PsameBase s P p q)
    (completeness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k))
    {h k : s.Hist} {p q : s.Pkg}
    (hp : s.InGapSig P D p h) (hq : s.InGapSig P D q k) :
    PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k) := by
  exact ExactGlobalizeBase_classify_iff
    (ExactGlobalizeBase_from_fields coverage soundness completeness) hp hq

theorem globalize_exact_base
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (coverage : forall h, s.InDom D h -> exists p, s.InGapSig P D p h)
    (soundness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      GeneratedSameSig s P h k -> PsameBase s P p q)
    (completeness : forall h k p q,
      s.InGapSig P D p h -> s.InGapSig P D q k ->
      PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) :
    ExactGlobalizeBase s P D /\
      forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k)) := by
  constructor
  case left =>
    exact ExactGlobalizeBase_from_fields coverage soundness completeness
  case right =>
    intro h k p q hp hq
    exact ExactGlobalizeBase_classify_iff
      (ExactGlobalizeBase_from_fields coverage soundness completeness) hp hq

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

theorem ExactGlobalizeBase_no_closure_export_directions
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
          PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k)) /\
      (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
          Nonempty (GeneratedSameSig s P h k) -> PsameBase s P p q) := by
  constructor
  case left =>
    intro h k p q hp hq base
    have exactness :
        PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k) :=
      ExactGlobalizeBase_no_closure_export ex hp hq
    exact exactness.mp base
  case right =>
    intro h k p q hp hq generated
    have exactness :
        PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k) :=
      ExactGlobalizeBase_no_closure_export ex hp hq
    exact exactness.mpr generated

theorem no_implicit_closure_exports_base
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

theorem NotExported_from_exact
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) : NotExported s P D ex := by
  intro h k p q hp hq
  exact ExactGlobalizeBase_classify_iff ex hp hq

theorem NotExported_classify_iff
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    {ex : ExactGlobalizeBase s P D}
    (notExported : NotExported s P D ex)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
      (PsameBase s P p q ↔ Nonempty (GeneratedSameSig s P h k)) := by
  intro hp hq
  exact notExported hp hq

theorem NotExported_relation_is_base
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    {ex : ExactGlobalizeBase s P D}
    (notExported : NotExported s P D ex)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h -> s.InGapSig P D q k ->
      (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k)) := by
  intro hp hq
  exact notExported hp hq

theorem NotExported_base_to_GeneratedSameSig
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    {ex : ExactGlobalizeBase s P D}
    (notExported : NotExported s P D ex)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
      PsameBase s P p q → Nonempty (GeneratedSameSig s P h k) := by
  intro hp hq base
  exact (notExported hp hq).mp base

theorem NotExported_GeneratedSameSig_to_base
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    {ex : ExactGlobalizeBase s P D}
    (notExported : NotExported s P D ex)
    {h k : s.Hist} {p q : s.Pkg} :
    s.InGapSig P D p h → s.InGapSig P D q k →
      Nonempty (GeneratedSameSig s P h k) → PsameBase s P p q := by
  intro hp hq gen
  exact (notExported hp hq).mpr gen

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

theorem ExactGlobalizeBase_public_export_shape
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain}
    (ex : ExactGlobalizeBase s P D) :
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))) := by
  constructor
  case left =>
    exact ex.coverage
  case right =>
    intro h k p q hp hq
    exact ExactGlobalizeBase_classify_iff ex hp hq

theorem ExactGlobalizeBase_export_from_fields
    {s : BaseReflectionSetup} {P : s.Pi} {D : s.Domain} :
    ((forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        GeneratedSameSig s P h k -> PsameBase s P p q) /\
      (forall h k p q, s.InGapSig P D p h -> s.InGapSig P D q k ->
        PsameBase s P p q -> Nonempty (GeneratedSameSig s P h k))) ->
    (forall h, s.InDom D h -> exists p, s.InGapSig P D p h) /\
      (forall {h k : s.Hist} {p q : s.Pkg},
        s.InGapSig P D p h -> s.InGapSig P D q k ->
        (PsameBase s P p q <-> Nonempty (GeneratedSameSig s P h k))) := by
  intro fields
  cases fields with
  | intro coverage rest =>
      cases rest with
      | intro soundness completeness =>
          exact And.intro coverage (by
            intro h k p q hp hq
            constructor
            case mp =>
              intro base
              exact completeness h k p q hp hq base
            case mpr =>
              intro generated
              cases generated with
              | intro gen =>
                  exact soundness h k p q hp hq gen)

end BEDC.BaseReflection
