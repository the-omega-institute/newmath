import BEDC.BaseReflection.Token
import BEDC.BaseReflection.Psame

namespace BEDC.BaseReflection

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

theorem base_package_reflection
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

theorem PackageReflection_base_from_policy
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (mode : PolicyTokenMode s P)
    {x y : s.SigObj} {p q : s.Pkg}
    (left : s.TokIntro P x p) (right : s.TokIntro P y q)
    (base : PsameBase s P p q) : s.hsame x y := by
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

theorem PackageReflection_token_unique_from_inversion
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {x y : s.SigObj} {p q : s.Pkg}
    (left : s.TokIntro P x p) (right : s.TokIntro P y q)
    (data : Nonempty (PBaseData s P p q)) : s.hsame x y := by
  cases data with
  | intro d =>
      exact PackageReflection_base_from_data eqv tok left right d

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

theorem PsameEqClosure_two_base_reflection
    {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) (tok : TokUnique s P)
    {x z : s.SigObj} {p q r : s.Pkg}
    (left : s.TokIntro P x p) (right : s.TokIntro P z r)
    (middle : Nonempty (Subtype (fun y : s.SigObj => s.TokIntro P y q)))
    (pq : PsameBase s P p q) (qr : PsameBase s P q r) : s.hsame x z := by
  cases middle with
  | intro mid =>
      exact eqv.trans
        (PackageReflection_base eqv tok left mid.property pq)
        (PackageReflection_base eqv tok mid.property right qr)

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

end BEDC.BaseReflection
