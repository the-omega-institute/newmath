import BEDC.BaseReflection.Core

namespace BEDC.BaseReflection

inductive PsameBase (s : BaseReflectionSetup) (P : s.Pi) : s.Pkg → s.Pkg → Prop where
  | intro {x y : s.SigObj} {p q : s.Pkg} :
      s.TokIntro P x p → s.TokIntro P y q → s.hsame x y → PsameBase s P p q

theorem PsameBase_constructor
    {s : BaseReflectionSetup} {P : s.Pi} {x y : s.SigObj} {p q : s.Pkg} :
    s.TokIntro P x p → s.TokIntro P y q → s.hsame x y → PsameBase s P p q := by
  intro left right same
  exact PsameBase.intro left right same

theorem PsameBase_refl_from_token {s : BaseReflectionSetup} {P : s.Pi}
    (eqv : HSameEquiv s) {x : s.SigObj} {p : s.Pkg} :
    s.TokIntro P x p → PsameBase s P p p := by
  intro introToken
  exact PsameBase.intro introToken introToken (eqv.refl x)

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

theorem PsameBase_single_constructor_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q → ∃ x : s.SigObj, ∃ y : s.SigObj,
      s.TokIntro P x p ∧ s.TokIntro P y q ∧ s.hsame x y := by
  intro base
  cases base with
  | intro left right same =>
      exact Exists.intro _ (Exists.intro _ (And.intro left (And.intro right same)))

theorem PsameBase_swapped_constructor_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} (eqv : HSameEquiv s) :
    PsameBase s P p q → ∃ y : s.SigObj, ∃ x : s.SigObj,
      s.TokIntro P y q ∧ s.TokIntro P x p ∧ s.hsame y x := by
  intro base
  cases base with
  | intro left right same =>
      exact Exists.intro _
        (Exists.intro _ (And.intro right (And.intro left (eqv.symm same))))

theorem PsameBase_iff_constructor_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q ↔ ∃ x : s.SigObj, ∃ y : s.SigObj,
      s.TokIntro P x p ∧ s.TokIntro P y q ∧ s.hsame x y := by
  constructor
  · exact PsameBase_single_constructor_witnesses
  · intro witness
    cases witness with
    | intro x rest =>
        cases rest with
        | intro y data =>
            cases data with
            | intro left tail =>
                cases tail with
                | intro right same =>
                    exact PsameBase.intro left right same

theorem PsameBase_token_intro_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q →
      (∃ x : s.SigObj, s.TokIntro P x p) ∧ (∃ y : s.SigObj, s.TokIntro P y q) := by
  intro base
  cases base with
  | intro left right same =>
      constructor
      · exact Exists.intro _ left
      · exact Exists.intro _ right

theorem PsameBase_left_token_witness
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q → ∃ x : s.SigObj, s.TokIntro P x p := by
  intro base
  cases base with
  | intro left right same =>
      exact Exists.intro _ left

theorem PsameBase_right_token_witness
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q → ∃ y : s.SigObj, s.TokIntro P y q := by
  intro base
  cases base with
  | intro left right same =>
      exact Exists.intro _ right

abbrev PsameSig (s : BaseReflectionSetup) (P : s.Pi) : s.Pkg → s.Pkg → Prop := PsameBase s P

theorem PsameSig_iff_PsameBase {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameSig s P p q <-> PsameBase s P p q := by
  rfl

theorem PsameSig_constructor
    {s : BaseReflectionSetup} {P : s.Pi} {x y : s.SigObj} {p q : s.Pkg} :
    s.TokIntro P x p → s.TokIntro P y q → s.hsame x y → PsameSig s P p q := by
  intro left right same
  exact PsameBase.intro left right same

theorem PsameSig_constructor_inversion
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameSig s P p q ->
      exists x : s.SigObj, exists y : s.SigObj,
        s.TokIntro P x p /\ s.TokIntro P y q /\ s.hsame x y := by
  intro base
  cases base with
  | intro left right same =>
      exact Exists.intro _ (Exists.intro _ (And.intro left (And.intro right same)))

theorem PsameSig_iff_constructor_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameSig s P p q ↔ ∃ x : s.SigObj, ∃ y : s.SigObj,
      s.TokIntro P x p ∧ s.TokIntro P y q ∧ s.hsame x y := by
  exact PsameBase_iff_constructor_witnesses

inductive PsameEqClosure (s : BaseReflectionSetup) (P : s.Pi) : s.Pkg → s.Pkg → Prop where
  | refl {p : s.Pkg} : PsameEqClosure s P p p
  | base {p q : s.Pkg} : PsameBase s P p q → PsameEqClosure s P p q
  | symm {p q : s.Pkg} : PsameEqClosure s P p q → PsameEqClosure s P q p
  | trans {p q r : s.Pkg} :
      PsameEqClosure s P p q → PsameEqClosure s P q r → PsameEqClosure s P p r

theorem PsameEqClosure_refl {s : BaseReflectionSetup} {P : s.Pi} (p : s.Pkg) :
    PsameEqClosure s P p p := by
  exact PsameEqClosure.refl

theorem PsameEqClosure_base_inclusion
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q -> PsameEqClosure s P p q := by
  intro base
  exact PsameEqClosure.base base

theorem PsameEqClosure_base_symm_inclusion {s : BaseReflectionSetup} {P : s.Pi}
    {p q : s.Pkg} :
    PsameBase s P p q → PsameEqClosure s P q p := by
  intro base
  exact PsameEqClosure.symm (PsameEqClosure.base base)

theorem PsameEqClosure_base_intro {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q → PsameEqClosure s P p q := by
  intro base
  exact PsameEqClosure.base base

theorem PsameEqClosure_symm {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameEqClosure s P p q -> PsameEqClosure s P q p := by
  intro h
  exact PsameEqClosure.symm h

theorem PsameEqClosure_trans {s : BaseReflectionSetup} {P : s.Pi} {p q r : s.Pkg} :
    PsameEqClosure s P p q -> PsameEqClosure s P q r -> PsameEqClosure s P p r := by
  intro left right
  exact PsameEqClosure.trans left right

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

theorem ClosureReflect_base_edge {s : BaseReflectionSetup} {P : s.Pi}
    (reflect : ClosureReflect s P) {x y : s.SigObj} {p q : s.Pkg} :
    s.TokIntro P x p → s.TokIntro P y q → PsameBase s P p q → s.hsame x y := by
  intro left right base
  exact reflect left right (PsameEqClosure.base base)

theorem ClosureReflect_apply {s : BaseReflectionSetup} {P : s.Pi}
    (reflect : ClosureReflect s P) {x y : s.SigObj} {p q : s.Pkg} :
    s.TokIntro P x p -> s.TokIntro P y q -> PsameEqClosure s P p q -> s.hsame x y := by
  intro left right closure
  exact reflect left right closure

structure PBaseData (s : BaseReflectionSetup) (P : s.Pi) (p q : s.Pkg) : Type where
  x : s.SigObj
  y : s.SigObj
  leftIntro : s.TokIntro P x p
  rightIntro : s.TokIntro P y q
  sigSame : s.hsame x y

theorem PBaseData_nonempty_from_witnesses {s : BaseReflectionSetup} {P : s.Pi}
    {p q : s.Pkg} {x y : s.SigObj} :
    s.TokIntro P x p -> s.TokIntro P y q -> s.hsame x y ->
      Nonempty (PBaseData s P p q) := by
  intro left right same
  exact Nonempty.intro {
    x := x
    y := y
    leftIntro := left
    rightIntro := right
    sigSame := same
  }

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

theorem psame_base_inversion {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q → Nonempty (PBaseData s P p q) := by
  intro h
  exact PsameBase_inversion h

theorem PsameBase_inversion_witness_object {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q →
      ∃ data : PBaseData s P p q,
        s.TokIntro P data.x p ∧ s.TokIntro P data.y q ∧ s.hsame data.x data.y := by
  intro base
  cases base with
  | intro left right same =>
      exact Exists.intro {
        x := _
        y := _
        leftIntro := left
        rightIntro := right
        sigSame := same
      } (And.intro left (And.intro right same))

theorem PsameBase_inversion_data_and_witnesses
    {s : BaseReflectionSetup} {P : s.Pi} {p q : s.Pkg} :
    PsameBase s P p q →
      Nonempty (PBaseData s P p q) ∧
        ∃ x : s.SigObj, ∃ y : s.SigObj,
          s.TokIntro P x p ∧ s.TokIntro P y q ∧ s.hsame x y := by
  intro base
  cases base with
  | intro left right same =>
      constructor
      · exact Nonempty.intro {
          x := _
          y := _
          leftIntro := left
          rightIntro := right
          sigSame := same
        }
      · exact Exists.intro _
          (Exists.intro _ (And.intro left (And.intro right same)))

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

end BEDC.BaseReflection
