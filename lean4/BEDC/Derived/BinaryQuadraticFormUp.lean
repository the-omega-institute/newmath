import BEDC.Derived.BinaryQuadFormUp

namespace BEDC.Derived.BinaryQuadraticFormUp

abbrev Z := BEDC.Derived.BinaryQuadFormUp.Z
abbrev Zeq := BEDC.Derived.BinaryQuadFormUp.Zeq
abbrev Zzero := BEDC.Derived.BinaryQuadFormUp.Zzero
abbrev Zone := BEDC.Derived.BinaryQuadFormUp.Zone
abbrev Zadd := BEDC.Derived.BinaryQuadFormUp.Zadd
abbrev Zmul := BEDC.Derived.BinaryQuadFormUp.Zmul
abbrev Zneg := BEDC.Derived.BinaryQuadFormUp.Zneg
abbrev zsub := BEDC.Derived.BinaryQuadFormUp.zsub
abbrev zsq := BEDC.Derived.BinaryQuadFormUp.zsq
abbrev zdouble := BEDC.Derived.BinaryQuadFormUp.zdouble
abbrev zfour := BEDC.Derived.BinaryQuadFormUp.zfour

abbrev BinaryQuadraticForm := BEDC.Derived.BinaryQuadFormUp.BinaryQuadForm
abbrev BinaryQuadraticFormEq := BEDC.Derived.BinaryQuadFormUp.BinaryQuadFormEq

def mk (a b c : Z) : BinaryQuadraticForm :=
  { a := a, b := b, c := c }

abbrev coefficientA (Q : BinaryQuadraticForm) : Z := Q.a
abbrev coefficientB (Q : BinaryQuadraticForm) : Z := Q.b
abbrev coefficientC (Q : BinaryQuadraticForm) : Z := Q.c

abbrev eval := BEDC.Derived.BinaryQuadFormUp.eval
abbrev discriminant := BEDC.Derived.BinaryQuadFormUp.discriminant
abbrev Represents := BEDC.Derived.BinaryQuadFormUp.Represents
abbrev zle := BEDC.Derived.BinaryQuadFormUp.zle
abbrev zabsLe := BEDC.Derived.BinaryQuadFormUp.zabsLe
abbrev Reduced := BEDC.Derived.BinaryQuadFormUp.Reduced

abbrev Matrix2Z := BEDC.Derived.MatrixUp.Mat2
abbrev SL2Z := BEDC.Derived.SL2Up.SL2
abbrev GeneratedSL2Step := BEDC.Derived.BinaryQuadFormUp.SL2Step

def transformByMatrix (M : Matrix2Z) (Q : BinaryQuadraticForm) :
    BinaryQuadraticForm :=
  { a := Zadd
      (Zadd (Zmul Q.a (zsq M.a00)) (Zmul Q.b (Zmul M.a00 M.a10)))
      (Zmul Q.c (zsq M.a10))
    b := Zadd
      (Zadd (Zmul (zdouble Q.a) (Zmul M.a00 M.a01))
        (Zmul Q.b
          (Zadd (Zmul M.a00 M.a11) (Zmul M.a01 M.a10))))
      (Zmul (zdouble Q.c) (Zmul M.a10 M.a11))
    c := Zadd
      (Zadd (Zmul Q.a (zsq M.a01)) (Zmul Q.b (Zmul M.a01 M.a11)))
      (Zmul Q.c (zsq M.a11)) }

def transformBySL2 (g : SL2Z) (Q : BinaryQuadraticForm) :
    BinaryQuadraticForm :=
  transformByMatrix g.mat Q

def SL2VariableSubstitutionRelated
    (Q P : BinaryQuadraticForm) : Prop :=
  ∃ g : SL2Z, BinaryQuadraticFormEq P (transformBySL2 g Q)

abbrev generatedStepToSL2 :=
  BEDC.Derived.BinaryQuadFormUp.SL2Step.toSL2

abbrev transformByGeneratedStep :=
  BEDC.Derived.BinaryQuadFormUp.actStep

abbrev transformByGeneratedWord :=
  BEDC.Derived.BinaryQuadFormUp.actWord

def GeneratedSL2WordRelated (Q P : BinaryQuadraticForm) : Prop :=
  ∃ steps : List GeneratedSL2Step,
    BinaryQuadraticFormEq P (transformByGeneratedWord steps Q)

theorem BinaryQuadraticFormEq_refl (Q : BinaryQuadraticForm) :
    BinaryQuadraticFormEq Q Q :=
  BEDC.Derived.BinaryQuadFormUp.BinaryQuadFormEq_refl Q

theorem BinaryQuadraticFormEq_symm {Q P : BinaryQuadraticForm} :
    BinaryQuadraticFormEq Q P -> BinaryQuadraticFormEq P Q :=
  BEDC.Derived.BinaryQuadFormUp.BinaryQuadFormEq_symm

theorem BinaryQuadraticFormEq_trans {Q P H : BinaryQuadraticForm} :
    BinaryQuadraticFormEq Q P ->
      BinaryQuadraticFormEq P H -> BinaryQuadraticFormEq Q H :=
  BEDC.Derived.BinaryQuadFormUp.BinaryQuadFormEq_trans

theorem discriminant_respects {Q P : BinaryQuadraticForm} :
    BinaryQuadraticFormEq Q P -> Zeq (discriminant Q) (discriminant P) :=
  BEDC.Derived.BinaryQuadFormUp.discriminant_respects

theorem generatedStep_discriminant
    (step : GeneratedSL2Step) (Q : BinaryQuadraticForm) :
    Zeq (discriminant (transformByGeneratedStep step Q)) (discriminant Q) :=
  BEDC.Derived.BinaryQuadFormUp.actStep_discriminant step Q

theorem generatedWord_discriminant
    (steps : List GeneratedSL2Step) (Q : BinaryQuadraticForm) :
    Zeq (discriminant (transformByGeneratedWord steps Q)) (discriminant Q) :=
  BEDC.Derived.BinaryQuadFormUp.actWord_discriminant steps Q

theorem GeneratedSL2WordRelated_refl (Q : BinaryQuadraticForm) :
    GeneratedSL2WordRelated Q Q := by
  exact ⟨[], BinaryQuadraticFormEq_refl Q⟩

theorem GeneratedSL2WordRelated_preserves_discriminant
    {Q P : BinaryQuadraticForm} :
    GeneratedSL2WordRelated Q P ->
      Zeq (discriminant P) (discriminant Q) := by
  intro related
  cases related with
  | intro steps same =>
      exact BEDC.Algebra.Rel.IntegerUp_RelCommRing.trans
        (discriminant_respects same)
        (generatedWord_discriminant steps Q)

theorem reduced_abs_middle_bound {Q : BinaryQuadraticForm} :
    Reduced Q -> zabsLe Q.b Q.a := by
  intro h
  exact h.left

theorem reduced_left_le_right {Q : BinaryQuadraticForm} :
    Reduced Q -> zle Q.a Q.c := by
  intro h
  exact h.right

theorem represents_intro (Q : BinaryQuadraticForm) (n x y : Z) :
    Zeq (eval Q x y) n -> Represents Q n := by
  intro h
  exact ⟨x, y, h⟩

theorem represents_elim {Q : BinaryQuadraticForm} {n : Z} :
    Represents Q n -> ∃ x y : Z, Zeq (eval Q x y) n := by
  intro h
  exact h

end BEDC.Derived.BinaryQuadraticFormUp
