import BEDC.Derived.PadicUp.IntegerTower.RingCompletion

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

theorem qpNat_add_pair_swap (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  calc
    (a + b) + (c + d) = a + (b + (c + d)) := Nat.add_assoc a b (c + d)
    _ = a + ((b + c) + d) :=
      congrArg (fun n => a + n) (Nat.add_assoc b c d).symm
    _ = a + ((c + b) + d) :=
      congrArg (fun n => a + (n + d)) (Nat.add_comm b c)
    _ = a + (c + (b + d)) := congrArg (fun n => a + n) (Nat.add_assoc c b d)
    _ = (a + c) + (b + d) := (Nat.add_assoc a c (b + d)).symm

theorem qpNat_trans_left (a b c d : Nat) :
    (b + d) + (a + c) = (a + b + c) + d := by
  calc
    (b + d) + (a + c) = (b + a) + (d + c) := qpNat_add_pair_swap b d a c
    _ = (a + b) + (d + c) := congrArg (fun n => n + (d + c)) (Nat.add_comm b a)
    _ = (a + b) + (c + d) :=
      congrArg (fun n => (a + b) + n) (Nat.add_comm d c)
    _ = ((a + b) + c) + d := (Nat.add_assoc (a + b) c d).symm
    _ = (a + b + c) + d := rfl

theorem qpNat_trans_right (a b c d : Nat) :
    (a + d) + (b + c) = (a + b + c) + d := by
  calc
    (a + d) + (b + c) = (a + b) + (d + c) := qpNat_add_pair_swap a d b c
    _ = (a + b) + (c + d) :=
      congrArg (fun n => (a + b) + n) (Nat.add_comm d c)
    _ = ((a + b) + c) + d := (Nat.add_assoc (a + b) c d).symm
    _ = (a + b + c) + d := rfl

theorem qpNat_add_term1_left (a b c d e : Nat) :
    ((a + b) + (c + d)) + e = (a + e + d) + (b + c) := by
  calc
    ((a + b) + (c + d)) + e = ((a + b) + c + d) + e :=
      congrArg (fun n => n + e) (Nat.add_assoc (a + b) c d).symm
    _ = ((a + b) + c) + (d + e) := Nat.add_assoc ((a + b) + c) d e
    _ = (a + b + c) + (d + e) := rfl
    _ = (a + (d + e)) + (b + c) := (qpNat_trans_right a b c (d + e)).symm
    _ = (a + (e + d)) + (b + c) :=
      congrArg (fun n => (a + n) + (b + c)) (Nat.add_comm d e)
    _ = (a + e + d) + (b + c) :=
      congrArg (fun n => n + (b + c)) (Nat.add_assoc a e d).symm

theorem qpNat_add_term1_right (a b c d e : Nat) :
    (a + e + d) + (b + c) = ((a + b) + (c + d)) + e :=
  (qpNat_add_term1_left a b c d e).symm

theorem qpNat_mul_respects_target (a b c d : Nat) :
    (a + c) + (b + d) = (a + b) + (c + d) :=
  (qpNat_add_pair_swap a b c d).symm

theorem qpNat_lift_left_one (a b c d e : Nat) :
    ((a + b) + (c + d)) + e = (b + e + d) + (a + c) := by
  calc
    ((a + b) + (c + d)) + e = ((a + b) + c + d) + e :=
      congrArg (fun n => n + e) (Nat.add_assoc (a + b) c d).symm
    _ = ((a + b) + c) + (d + e) := Nat.add_assoc ((a + b) + c) d e
    _ = (a + b + c) + (d + e) := rfl
    _ = a + b + (c + (d + e)) := Nat.add_assoc (a + b) c (d + e)
    _ = (a + c) + (b + (d + e)) := qpNat_add_pair_swap a b c (d + e)
    _ = (b + (d + e)) + (a + c) := Nat.add_comm (a + c) (b + (d + e))
    _ = (b + (e + d)) + (a + c) :=
      congrArg (fun n => (b + n) + (a + c)) (Nat.add_comm d e)
    _ = (b + e + d) + (a + c) :=
      congrArg (fun n => n + (a + c)) (Nat.add_assoc b e d).symm

theorem qpNat_lift_right_one (a b c d e : Nat) :
    (b + d + e) + (a + c) = ((a + b) + (c + d)) + e := by
  calc
    (b + d + e) + (a + c) = (b + (d + e)) + (a + c) :=
      congrArg (fun n => n + (a + c)) (Nat.add_assoc b d e)
    _ = (a + c) + (b + (d + e)) := Nat.add_comm (b + (d + e)) (a + c)
    _ = a + b + (c + (d + e)) := (qpNat_add_pair_swap a b c (d + e)).symm
    _ = (a + b + c) + (d + e) := (Nat.add_assoc (a + b) c (d + e)).symm
    _ = ((a + b) + c) + (d + e) := rfl
    _ = ((a + b) + c + d) + e := (Nat.add_assoc ((a + b) + c) d e).symm
    _ = ((a + b) + (c + d)) + e :=
      congrArg (fun n => n + e) (Nat.add_assoc (a + b) c d)

theorem qpNat_lift_left_pair (a b c d e : Nat) :
    ((a + b) + (c + d)) + e = (a + c + e) + (b + d) := by
  calc
    ((a + b) + (c + d)) + e = ((a + c) + (b + d)) + e :=
      congrArg (fun n => n + e) (qpNat_add_pair_swap a b c d)
    _ = (a + c) + ((b + d) + e) := Nat.add_assoc (a + c) (b + d) e
    _ = (a + c) + (e + (b + d)) :=
      congrArg (fun n => (a + c) + n) (Nat.add_comm (b + d) e)
    _ = ((a + c) + e) + (b + d) := (Nat.add_assoc (a + c) e (b + d)).symm
    _ = (a + c + e) + (b + d) := rfl

theorem qpNat_lift_left_pair_swap (a b c d e : Nat) :
    ((a + b) + (c + d)) + e = (a + e + c) + (b + d) := by
  have first := qpNat_lift_left_pair a b c d e
  have inner : a + c + e = a + e + c := by
    calc
      a + c + e = a + (c + e) := Nat.add_assoc a c e
      _ = a + (e + c) := congrArg (fun n => a + n) (Nat.add_comm c e)
      _ = a + e + c := (Nat.add_assoc a e c).symm
  exact Eq.trans first (congrArg (fun n => n + (b + d)) inner)

theorem qpNat_right_distrib_shift (i j k : Nat) :
    (i + j) + (i + k) = (i + (j + k)) + i := by
  calc
    (i + j) + (i + k) = (i + i) + (j + k) := qpNat_add_pair_swap i j i k
    _ = (i + (j + k)) + i := by
      calc
        (i + i) + (j + k) = i + (i + (j + k)) := Nat.add_assoc i i (j + k)
        _ = i + ((j + k) + i) := congrArg (fun n => i + n) (Nat.add_comm i (j + k))
        _ = i + (j + k) + i := (Nat.add_assoc i (j + k) i).symm

def pUnitZp (p : BHist) (prime : NatPrime p) : ZpInt p :=
  natToZp p prime p prime.left

def pPowZp (p : BHist) (prime : NatPrime p) : Nat -> ZpInt p
  | 0 => zpOne p prime
  | n + 1 => zpMul p (pPowZp p prime n) (pUnitZp p prime)

theorem zpAdd_congr {p : BHist} {x x' y y' : ZpInt p} :
    ZpEq x x' -> ZpEq y y' ->
      ZpEq (zpAdd p x y) (zpAdd p x' y') := by
  intro sameX sameY N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (append (x.trunc N NUnary).val (y.trunc N NUnary).val))
    (natModFn (pPowCanon p N)
      (append (x'.trunc N NUnary).val (y'.trunc N NUnary).val))
  exact natModFn_append_hsame_transport (sameX N NUnary) (sameY N NUnary)

theorem zpMul_congr {p : BHist} {x x' y y' : ZpInt p} :
    ZpEq x x' -> ZpEq y y' ->
      ZpEq (zpMul p x y) (zpMul p x' y') := by
  intro sameX sameY N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val))
    (natModFn (pPowCanon p N)
      (natMulFn (x'.trunc N NUnary).val (y'.trunc N NUnary).val))
  exact natModFn_hsame_arg_transport (M := pPowCanon p N)
    (natMulFn_hsame_transport (sameX N NUnary) (sameY N NUnary))

theorem zpMul_left_congr {p : BHist} {x x' y : ZpInt p} :
    ZpEq x x' -> ZpEq (zpMul p x y) (zpMul p x' y) := by
  intro sameX
  exact zpMul_congr sameX (ZpEq_refl y)

theorem zpMul_right_congr {p : BHist} {x y y' : ZpInt p} :
    ZpEq y y' -> ZpEq (zpMul p x y) (zpMul p x y') := by
  intro sameY
  exact zpMul_congr (ZpEq_refl x) sameY

theorem zpMul_zero_right (p : BHist) (x : ZpInt p) :
    ZpEq (zpMul p x (zpZero p x.prime)) (zpZero p x.prime) := by
  intro N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (natMulFn (x.trunc N NUnary).val (natModFn (pPowCanon p N) BHist.Empty)))
    (natModFn (pPowCanon p N) BHist.Empty)
  rfl

theorem zpMul_zero_left (p : BHist) (prime : NatPrime p) (x : ZpInt p) :
    ZpEq (zpMul p (zpZero p prime) x) (zpZero p prime) := by
  exact ZpEq_trans (zpMul_comm p (zpZero p prime) x)
    (zpMul_zero_right p x)

theorem zpZero_prime_irrel {p : BHist} (prime prime' : NatPrime p) :
    ZpEq (zpZero p prime) (zpZero p prime') := by
  intro N NUnary
  rfl

theorem pPowZp_mul_add (p : BHist) (prime : NatPrime p) (a b : Nat) :
    ZpEq (zpMul p (pPowZp p prime a) (pPowZp p prime b))
      (pPowZp p prime (a + b)) := by
  induction b with
  | zero =>
      rw [Nat.add_zero]
      exact zpOne_mul_right p prime (pPowZp p prime a)
  | succ b ih =>
      rw [Nat.add_succ]
      change ZpEq
        (zpMul p (pPowZp p prime a)
          (zpMul p (pPowZp p prime b) (pUnitZp p prime)))
        (zpMul p (pPowZp p prime (a + b)) (pUnitZp p prime))
      exact ZpEq_trans
        (ZpEq_symm (zpMul_assoc p (pPowZp p prime a)
          (pPowZp p prime b) (pUnitZp p prime)))
        (zpMul_left_congr ih)

theorem pPowZp_prime_irrel {p : BHist} (prime prime' : NatPrime p) (n : Nat) :
    ZpEq (pPowZp p prime n) (pPowZp p prime' n) := by
  induction n with
  | zero =>
      intro N NUnary
      rfl
  | succ n ih =>
      change ZpEq (zpMul p (pPowZp p prime n) (pUnitZp p prime))
        (zpMul p (pPowZp p prime' n) (pUnitZp p prime'))
      exact zpMul_congr ih (by intro N NUnary; rfl)

def zpScale (p : BHist) (prime : NatPrime p) (n : Nat) (x : ZpInt p) : ZpInt p :=
  zpMul p (pPowZp p prime n) x

theorem zpScale_prime_irrel {p : BHist} (prime prime' : NatPrime p) (n : Nat)
    (x : ZpInt p) :
    ZpEq (zpScale p prime n x) (zpScale p prime' n x) := by
  unfold zpScale
  exact zpMul_left_congr (pPowZp_prime_irrel prime prime' n)

theorem zpScale_congr {p : BHist} (prime : NatPrime p) {n : Nat} {x y : ZpInt p} :
    ZpEq x y -> ZpEq (zpScale p prime n x) (zpScale p prime n y) := by
  intro same
  exact zpMul_right_congr same

theorem zpScale_scale (p : BHist) (prime : NatPrime p) (a b : Nat) (x : ZpInt p) :
    ZpEq (zpScale p prime a (zpScale p prime b x))
      (zpScale p prime (a + b) x) := by
  unfold zpScale
  exact ZpEq_trans
    (ZpEq_symm (zpMul_assoc p (pPowZp p prime a) (pPowZp p prime b) x))
    (zpMul_left_congr (pPowZp_mul_add p prime a b))

theorem zpScale_nat_eq {p : BHist} (prime : NatPrime p) {a b : Nat} (x : ZpInt p) :
    a = b -> ZpEq (zpScale p prime a x) (zpScale p prime b x) := by
  intro same
  cases same
  exact ZpEq_refl _

theorem zpScale_scale_to (p : BHist) (prime : NatPrime p)
    (a b c : Nat) (x : ZpInt p) :
    a + b = c -> ZpEq (zpScale p prime a (zpScale p prime b x))
      (zpScale p prime c x) := by
  intro same
  exact ZpEq_trans (zpScale_scale p prime a b x)
    (zpScale_nat_eq prime x same)

theorem zpScale_nested_reindex (p : BHist) (prime : NatPrime p)
    (a b c d : Nat) (x : ZpInt p) :
    a + b = c + d ->
      ZpEq (zpScale p prime a (zpScale p prime b x))
        (zpScale p prime c (zpScale p prime d x)) := by
  intro same
  exact ZpEq_trans (zpScale_scale p prime a b x)
    (ZpEq_trans (zpScale_nat_eq prime x same)
      (ZpEq_symm (zpScale_scale p prime c d x)))

theorem zpMul_pair_shuffle (p : BHist) (a b c d : ZpInt p) :
    ZpEq (zpMul p (zpMul p a b) (zpMul p c d))
      (zpMul p (zpMul p a c) (zpMul p b d)) := by
  exact ZpEq_trans
    (zpMul_assoc p a b (zpMul p c d))
    (ZpEq_trans
      (zpMul_right_congr (ZpEq_symm (zpMul_assoc p b c d)))
      (ZpEq_trans
        (zpMul_right_congr
          (zpMul_left_congr (zpMul_comm p b c)))
        (ZpEq_trans
          (zpMul_right_congr (zpMul_assoc p c b d))
          (ZpEq_symm (zpMul_assoc p a c (zpMul p b d))))))

theorem zpScale_mul_split (p : BHist) (prime : NatPrime p)
    (r s : Nat) (x y : ZpInt p) :
    ZpEq (zpScale p prime (r + s) (zpMul p x y))
      (zpMul p (zpScale p prime r x) (zpScale p prime s y)) := by
  unfold zpScale
  exact ZpEq_trans
    (zpMul_left_congr (ZpEq_symm (pPowZp_mul_add p prime r s)))
    (zpMul_pair_shuffle p (pPowZp p prime r) (pPowZp p prime s) x y)

theorem zpScale_mul_split_to (p : BHist) (prime : NatPrime p)
    (r s c : Nat) (x y : ZpInt p) :
    r + s = c ->
      ZpEq (zpScale p prime c (zpMul p x y))
        (zpMul p (zpScale p prime r x) (zpScale p prime s y)) := by
  intro sumEq
  exact ZpEq_trans (zpScale_nat_eq prime (zpMul p x y) (sumEq.symm))
    (zpScale_mul_split p prime r s x y)

theorem zpMul_scale_right (p : BHist) (prime : NatPrime p) (n : Nat)
    (x y : ZpInt p) :
    ZpEq (zpMul p x (zpScale p prime n y))
      (zpScale p prime n (zpMul p x y)) := by
  unfold zpScale
  exact ZpEq_trans
    (ZpEq_symm (zpMul_assoc p x (pPowZp p prime n) y))
    (ZpEq_trans
      (zpMul_left_congr (zpMul_comm p x (pPowZp p prime n)))
      (zpMul_assoc p (pPowZp p prime n) x y))

theorem zpScale_add_distrib (p : BHist) (prime : NatPrime p)
    (n : Nat) (x y : ZpInt p) :
    ZpEq (zpScale p prime n (zpAdd p x y))
      (zpAdd p (zpScale p prime n x) (zpScale p prime n y)) := by
  unfold zpScale
  exact zpMul_add_distrib p (pPowZp p prime n) x y

theorem zpScale_zero (p : BHist) (prime zeroPrime : NatPrime p) (n : Nat) :
    ZpEq (zpScale p prime n (zpZero p zeroPrime)) (zpZero p zeroPrime) := by
  unfold zpScale
  exact ZpEq_trans (zpMul_zero_right p (pPowZp p prime n))
    (zpZero_prime_irrel (pPowZp p prime n).prime zeroPrime)

structure QpInt (p : BHist) where
  shift : Nat
  value : ZpInt p

def zpToQp {p : BHist} (z : ZpInt p) : QpInt p :=
  { shift := 0, value := z }

def QpCrossEq {p : BHist} (prime : NatPrime p) (x y : QpInt p) : Prop :=
  ZpEq (zpScale p prime y.shift x.value) (zpScale p prime x.shift y.value)

def QpEq {p : BHist} (x y : QpInt p) : Prop :=
  ∀ prime : NatPrime p, ∃ pad : Nat,
    ZpEq (zpScale p prime (pad + y.shift) x.value)
      (zpScale p prime (pad + x.shift) y.value)

theorem QpCrossEq_to_QpEq {p : BHist} {x y : QpInt p} :
    (∀ prime : NatPrime p, QpCrossEq prime x y) -> QpEq x y := by
  intro cross prime
  exact ⟨0, by simpa using cross prime⟩

theorem QpEq_refl {p : BHist} (x : QpInt p) : QpEq x x := by
  intro prime
  exact ⟨0, ZpEq_refl _⟩

theorem QpEq_symm {p : BHist} {x y : QpInt p} :
    QpEq x y -> QpEq y x := by
  intro same prime
  cases same prime with
  | intro pad padSame =>
      exact ⟨pad, ZpEq_symm padSame⟩

theorem QpEq_trans {p : BHist} {x y z : QpInt p} :
    QpEq x y -> QpEq y z -> QpEq x z := by
  intro sameXY sameYZ prime
  cases sameXY prime with
  | intro padXY eqXY =>
      cases sameYZ prime with
      | intro padYZ eqYZ =>
          let pad := padXY + padYZ + y.shift
          have leftLift :
              ZpEq
                (zpScale p prime (padYZ + z.shift)
                  (zpScale p prime (padXY + y.shift) x.value))
                (zpScale p prime (padYZ + z.shift)
                  (zpScale p prime (padXY + x.shift) y.value)) :=
            zpScale_congr prime eqXY
          have rightLift :
              ZpEq
                (zpScale p prime (padXY + x.shift)
                  (zpScale p prime (padYZ + z.shift) y.value))
                (zpScale p prime (padXY + x.shift)
                  (zpScale p prime (padYZ + y.shift) z.value)) :=
            zpScale_congr prime eqYZ
          have middleSwap :
              ZpEq
                (zpScale p prime (padYZ + z.shift)
                  (zpScale p prime (padXY + x.shift) y.value))
                (zpScale p prime (padXY + x.shift)
                  (zpScale p prime (padYZ + z.shift) y.value)) := by
            exact ZpEq_trans
              (zpScale_scale p prime (padYZ + z.shift) (padXY + x.shift) y.value)
              (ZpEq_trans
                (zpScale_nat_eq prime y.value (by
                  rw [Nat.add_comm (padYZ + z.shift) (padXY + x.shift)]))
                (ZpEq_symm
                  (zpScale_scale p prime (padXY + x.shift) (padYZ + z.shift) y.value)))
          have chain :=
            ZpEq_trans leftLift (ZpEq_trans middleSwap rightLift)
          have leftTarget :
              ZpEq
                (zpScale p prime (pad + z.shift) x.value)
                (zpScale p prime (padYZ + z.shift)
                  (zpScale p prime (padXY + y.shift) x.value)) := by
            exact ZpEq_symm
              (zpScale_scale_to p prime (padYZ + z.shift) (padXY + y.shift)
                (pad + z.shift) x.value
                (qpNat_trans_left padXY padYZ y.shift z.shift))
          have rightTarget :
              ZpEq
                (zpScale p prime (padXY + x.shift)
                  (zpScale p prime (padYZ + y.shift) z.value))
                (zpScale p prime (pad + x.shift) z.value) := by
            exact zpScale_scale_to p prime (padXY + x.shift) (padYZ + y.shift)
              (pad + x.shift) z.value
              (qpNat_trans_right padXY padYZ y.shift x.shift)
          exact ⟨pad, ZpEq_trans leftTarget (ZpEq_trans chain rightTarget)⟩

theorem QpEq_of_shift_value {p : BHist} {x y : QpInt p} :
    x.shift = y.shift -> ZpEq x.value y.value -> QpEq x y := by
  intro shiftEq valueEq prime
  exact ⟨0, by
    rw [Nat.zero_add, Nat.zero_add]
    rw [← shiftEq]
    exact zpScale_congr prime valueEq⟩

def qpZero (p : BHist) (prime : NatPrime p) : QpInt p :=
  { shift := 0, value := zpZero p prime }

def qpOne (p : BHist) (prime : NatPrime p) : QpInt p :=
  { shift := 0, value := zpOne p prime }

def qpNeg {p : BHist} (x : QpInt p) : QpInt p :=
  { shift := x.shift, value := zpNeg p x.value }

def qpMul {p : BHist} (x y : QpInt p) : QpInt p :=
  { shift := x.shift + y.shift, value := zpMul p x.value y.value }

def qpAdd {p : BHist} (x y : QpInt p) : QpInt p :=
  { shift := x.shift + y.shift
    value :=
      zpAdd p
        (zpMul p (pPowZp p x.value.prime y.shift) x.value)
        (zpMul p (pPowZp p x.value.prime x.shift) y.value) }

def qpRescale {p : BHist} (n : Nat) (x : QpInt p) : QpInt p :=
  { shift := x.shift + n, value := zpScale p x.value.prime n x.value }

theorem qpAdd_value_canonical {p : BHist} (prime : NatPrime p) (x y : QpInt p) :
    ZpEq (qpAdd x y).value
      (zpAdd p
        (zpScale p prime y.shift x.value)
        (zpScale p prime x.shift y.value)) := by
  unfold qpAdd zpScale
  dsimp
  exact zpAdd_congr
    (zpMul_left_congr (pPowZp_prime_irrel x.value.prime prime y.shift))
    (zpMul_left_congr (pPowZp_prime_irrel x.value.prime prime x.shift))

theorem qpRescale_eq {p : BHist} (n : Nat) (x : QpInt p) :
    QpEq (qpRescale n x) x := by
  intro prime
  exact ⟨0, by
    rw [Nat.zero_add, Nat.zero_add]
    unfold qpRescale
    dsimp
    have innerPrime :
        ZpEq (zpScale p prime x.shift (zpScale p x.value.prime n x.value))
          (zpScale p prime x.shift (zpScale p prime n x.value)) :=
      zpScale_congr prime (zpScale_prime_irrel x.value.prime prime n x.value)
    exact ZpEq_trans innerPrime
      (zpScale_scale p prime x.shift n x.value)⟩

theorem qpMul_comm {p : BHist} (x y : QpInt p) :
    QpEq (qpMul x y) (qpMul y x) := by
  apply QpEq_of_shift_value
  · exact Nat.add_comm x.shift y.shift
  · unfold qpMul
    dsimp
    exact zpMul_comm p x.value y.value

theorem qpMul_assoc {p : BHist} (x y z : QpInt p) :
    QpEq (qpMul (qpMul x y) z) (qpMul x (qpMul y z)) := by
  apply QpEq_of_shift_value
  · exact Nat.add_assoc x.shift y.shift z.shift
  · unfold qpMul
    dsimp
    exact zpMul_assoc p x.value y.value z.value

theorem qpOne_mul_left (p : BHist) (prime : NatPrime p) (x : QpInt p) :
    QpEq (qpMul (qpOne p prime) x) x := by
  intro prime'
  exact ⟨0, by
    rw [Nat.zero_add, Nat.zero_add]
    unfold qpMul qpOne
    dsimp
    rw [Nat.zero_add]
    exact zpScale_congr prime' (zpOne_mul_left p prime x.value)⟩

theorem qpOne_mul_right (p : BHist) (prime : NatPrime p) (x : QpInt p) :
    QpEq (qpMul x (qpOne p prime)) x := by
  exact QpEq_trans (qpMul_comm x (qpOne p prime))
    (qpOne_mul_left p prime x)

theorem qpMul_respects {p : BHist} {x x' y y' : QpInt p} :
    QpEq x x' -> QpEq y y' ->
      QpEq (qpMul x y) (qpMul x' y') := by
  intro sameX sameY prime
  cases sameX prime with
  | intro padX eqX =>
      cases sameY prime with
      | intro padY eqY =>
          let pad := padX + padY
          have leftSplit :
              ZpEq
                (zpScale p prime (pad + (x'.shift + y'.shift))
                  (zpMul p x.value y.value))
                (zpMul p
                  (zpScale p prime (padX + x'.shift) x.value)
                  (zpScale p prime (padY + y'.shift) y.value)) := by
            exact zpScale_mul_split_to p prime (padX + x'.shift)
              (padY + y'.shift) (pad + (x'.shift + y'.shift))
              x.value y.value
              (qpNat_mul_respects_target padX padY x'.shift y'.shift)
          have middle :
              ZpEq
                (zpMul p
                  (zpScale p prime (padX + x'.shift) x.value)
                  (zpScale p prime (padY + y'.shift) y.value))
                (zpMul p
                  (zpScale p prime (padX + x.shift) x'.value)
                  (zpScale p prime (padY + y.shift) y'.value)) :=
            zpMul_congr eqX eqY
          have rightSplit :
              ZpEq
                (zpMul p
                  (zpScale p prime (padX + x.shift) x'.value)
                  (zpScale p prime (padY + y.shift) y'.value))
                (zpScale p prime (pad + (x.shift + y.shift))
                  (zpMul p x'.value y'.value)) := by
            exact ZpEq_symm
              (zpScale_mul_split_to p prime (padX + x.shift)
                (padY + y.shift) (pad + (x.shift + y.shift))
                x'.value y'.value
                (qpNat_mul_respects_target padX padY x.shift y.shift))
          exact ⟨pad, ZpEq_trans leftSplit (ZpEq_trans middle rightSplit)⟩

theorem qpAdd_respects {p : BHist} {x x' y y' : QpInt p} :
    QpEq x x' -> QpEq y y' ->
      QpEq (qpAdd x y) (qpAdd x' y') := by
  intro sameX sameY prime
  cases sameX prime with
  | intro padX eqX =>
      cases sameY prime with
      | intro padY eqY =>
          let pad := padX + padY
          let leftShift := pad + (x'.shift + y'.shift)
          let rightShift := pad + (x.shift + y.shift)
          have leftCanon :
              ZpEq (zpScale p prime leftShift (qpAdd x y).value)
                (zpAdd p
                  (zpScale p prime leftShift (zpScale p prime y.shift x.value))
                  (zpScale p prime leftShift (zpScale p prime x.shift y.value))) := by
            exact ZpEq_trans
              (zpScale_congr prime (qpAdd_value_canonical prime x y))
              (zpScale_add_distrib p prime leftShift
                (zpScale p prime y.shift x.value)
                (zpScale p prime x.shift y.value))
          have rightCanon :
              ZpEq (zpScale p prime rightShift (qpAdd x' y').value)
                (zpAdd p
                  (zpScale p prime rightShift (zpScale p prime y'.shift x'.value))
                  (zpScale p prime rightShift (zpScale p prime x'.shift y'.value))) := by
            exact ZpEq_trans
              (zpScale_congr prime (qpAdd_value_canonical prime x' y'))
              (zpScale_add_distrib p prime rightShift
                (zpScale p prime y'.shift x'.value)
                (zpScale p prime x'.shift y'.value))
          have xLeft :
              ZpEq
                (zpScale p prime leftShift (zpScale p prime y.shift x.value))
                (zpScale p prime (padY + y.shift + y'.shift)
                  (zpScale p prime (padX + x'.shift) x.value)) := by
            dsimp [leftShift, pad]
            exact zpScale_nested_reindex p prime
              ((padX + padY) + (x'.shift + y'.shift)) y.shift
              (padY + y.shift + y'.shift) (padX + x'.shift) x.value
              (qpNat_lift_left_one padX padY x'.shift y'.shift y.shift)
          have xMiddle :
              ZpEq
                (zpScale p prime (padY + y.shift + y'.shift)
                  (zpScale p prime (padX + x'.shift) x.value))
                (zpScale p prime (padY + y.shift + y'.shift)
                  (zpScale p prime (padX + x.shift) x'.value)) :=
            zpScale_congr prime eqX
          have xRight :
              ZpEq
                (zpScale p prime (padY + y.shift + y'.shift)
                  (zpScale p prime (padX + x.shift) x'.value))
                (zpScale p prime rightShift (zpScale p prime y'.shift x'.value)) := by
            dsimp [rightShift, pad]
            exact zpScale_nested_reindex p prime
              (padY + y.shift + y'.shift) (padX + x.shift)
              ((padX + padY) + (x.shift + y.shift)) y'.shift x'.value
              (qpNat_lift_right_one padX padY x.shift y.shift y'.shift)
          have xTerm :
              ZpEq
                (zpScale p prime leftShift (zpScale p prime y.shift x.value))
                (zpScale p prime rightShift (zpScale p prime y'.shift x'.value)) :=
            ZpEq_trans xLeft (ZpEq_trans xMiddle xRight)
          have yLeft :
              ZpEq
                (zpScale p prime leftShift (zpScale p prime x.shift y.value))
                (zpScale p prime (padX + x.shift + x'.shift)
                  (zpScale p prime (padY + y'.shift) y.value)) := by
            dsimp [leftShift, pad]
            exact zpScale_nested_reindex p prime
              ((padX + padY) + (x'.shift + y'.shift)) x.shift
              (padX + x.shift + x'.shift) (padY + y'.shift) y.value
              (qpNat_lift_left_pair_swap padX padY x'.shift y'.shift x.shift)
          have yMiddle :
              ZpEq
                (zpScale p prime (padX + x.shift + x'.shift)
                  (zpScale p prime (padY + y'.shift) y.value))
                (zpScale p prime (padX + x.shift + x'.shift)
                  (zpScale p prime (padY + y.shift) y'.value)) :=
            zpScale_congr prime eqY
          have yRight :
              ZpEq
                (zpScale p prime (padX + x.shift + x'.shift)
                  (zpScale p prime (padY + y.shift) y'.value))
                (zpScale p prime rightShift (zpScale p prime x'.shift y'.value)) := by
            dsimp [rightShift, pad]
            exact zpScale_nested_reindex p prime
              (padX + x.shift + x'.shift) (padY + y.shift)
              ((padX + padY) + (x.shift + y.shift)) x'.shift y'.value
              (Eq.symm (qpNat_lift_left_pair padX padY x.shift y.shift x'.shift))
          have yTerm :
              ZpEq
                (zpScale p prime leftShift (zpScale p prime x.shift y.value))
                (zpScale p prime rightShift (zpScale p prime x'.shift y'.value)) :=
            ZpEq_trans yLeft (ZpEq_trans yMiddle yRight)
          have middle :
              ZpEq
                (zpAdd p
                  (zpScale p prime leftShift (zpScale p prime y.shift x.value))
                  (zpScale p prime leftShift (zpScale p prime x.shift y.value)))
                (zpAdd p
                  (zpScale p prime rightShift (zpScale p prime y'.shift x'.value))
                  (zpScale p prime rightShift (zpScale p prime x'.shift y'.value))) :=
            zpAdd_congr xTerm yTerm
          exact ⟨pad, ZpEq_trans leftCanon (ZpEq_trans middle (ZpEq_symm rightCanon))⟩

theorem qpAdd_assoc {p : BHist} (x y z : QpInt p) :
    QpEq (qpAdd (qpAdd x y) z) (qpAdd x (qpAdd y z)) := by
  apply QpEq_of_shift_value
  · exact Nat.add_assoc x.shift y.shift z.shift
  · let A := zpScale p x.value.prime z.shift (zpScale p x.value.prime y.shift x.value)
    let B := zpScale p x.value.prime z.shift (zpScale p x.value.prime x.shift y.value)
    let C := zpScale p x.value.prime (x.shift + y.shift) z.value
    let A' := zpScale p x.value.prime (y.shift + z.shift) x.value
    let B' := zpScale p x.value.prime x.shift (zpScale p x.value.prime z.shift y.value)
    let C' := zpScale p x.value.prime x.shift (zpScale p x.value.prime y.shift z.value)
    have leftCanon :
        ZpEq (qpAdd (qpAdd x y) z).value
          (zpAdd p (zpScale p x.value.prime z.shift (qpAdd x y).value)
            (zpScale p x.value.prime (x.shift + y.shift) z.value)) := by
      exact qpAdd_value_canonical x.value.prime (qpAdd x y) z
    have rightCanon :
        ZpEq (qpAdd x (qpAdd y z)).value
          (zpAdd p (zpScale p x.value.prime (y.shift + z.shift) x.value)
            (zpScale p x.value.prime x.shift (qpAdd y z).value)) := by
      exact qpAdd_value_canonical x.value.prime x (qpAdd y z)
    have xyExpand :
        ZpEq (zpScale p x.value.prime z.shift (qpAdd x y).value)
          (zpAdd p A B) := by
      exact ZpEq_trans
        (zpScale_congr x.value.prime (qpAdd_value_canonical x.value.prime x y))
        (zpScale_add_distrib p x.value.prime z.shift
          (zpScale p x.value.prime y.shift x.value)
          (zpScale p x.value.prime x.shift y.value))
    have yzExpand :
        ZpEq (zpScale p x.value.prime x.shift (qpAdd y z).value)
          (zpAdd p B' C') := by
      exact ZpEq_trans
        (zpScale_congr x.value.prime (qpAdd_value_canonical x.value.prime y z))
        (zpScale_add_distrib p x.value.prime x.shift
          (zpScale p x.value.prime z.shift y.value)
          (zpScale p x.value.prime y.shift z.value))
    have leftToABC :
        ZpEq
          (zpAdd p (zpScale p x.value.prime z.shift (qpAdd x y).value)
            (zpScale p x.value.prime (x.shift + y.shift) z.value))
          (zpAdd p (zpAdd p A B) C) := by
      exact zpAdd_congr xyExpand (ZpEq_refl C)
    have assocABC :
        ZpEq (zpAdd p (zpAdd p A B) C) (zpAdd p A (zpAdd p B C)) :=
      zpAdd_assoc p A B C
    have Aeq : ZpEq A A' := by
      unfold A A'
      exact zpScale_scale_to p x.value.prime z.shift y.shift (y.shift + z.shift)
        x.value (Nat.add_comm z.shift y.shift)
    have Beq : ZpEq B B' := by
      unfold B B'
      exact zpScale_nested_reindex p x.value.prime z.shift x.shift x.shift z.shift
        y.value (Nat.add_comm z.shift x.shift)
    have Ceq : ZpEq C C' := by
      unfold C C'
      exact ZpEq_symm (zpScale_scale p x.value.prime x.shift y.shift z.value)
    have ABCtoRightTerms :
        ZpEq (zpAdd p A (zpAdd p B C)) (zpAdd p A' (zpAdd p B' C')) :=
      zpAdd_congr Aeq (zpAdd_congr Beq Ceq)
    have rightTermsToRight :
        ZpEq (zpAdd p A' (zpAdd p B' C'))
          (zpAdd p (zpScale p x.value.prime (y.shift + z.shift) x.value)
            (zpScale p x.value.prime x.shift (qpAdd y z).value)) := by
      unfold A'
      exact zpAdd_congr (ZpEq_refl _) (ZpEq_symm yzExpand)
    exact ZpEq_trans leftCanon
      (ZpEq_trans leftToABC
        (ZpEq_trans assocABC
          (ZpEq_trans ABCtoRightTerms
            (ZpEq_trans rightTermsToRight (ZpEq_symm rightCanon)))))

theorem qpAdd_comm {p : BHist} (x y : QpInt p) :
    QpEq (qpAdd x y) (qpAdd y x) := by
  apply QpEq_of_shift_value
  · exact Nat.add_comm x.shift y.shift
  · unfold qpAdd
    dsimp
    exact zpAdd_comm p
      (zpMul p (pPowZp p x.value.prime y.shift) x.value)
      (zpMul p (pPowZp p x.value.prime x.shift) y.value)

theorem qpZero_add_left (p : BHist) (prime : NatPrime p) (x : QpInt p) :
    QpEq (qpAdd (qpZero p prime) x) x := by
  intro prime'
  exact ⟨0, by
    rw [Nat.zero_add, Nat.zero_add]
    unfold qpAdd qpZero
    dsimp
    rw [Nat.zero_add]
    have leftZero :
        ZpEq (zpMul p (pPowZp p prime x.shift) (zpZero p prime))
          (zpZero p prime) :=
      zpMul_zero_right p (pPowZp p prime x.shift)
    have rightOne :
        ZpEq (zpMul p (pPowZp p prime 0) x.value) x.value :=
      zpOne_mul_left p prime x.value
    exact ZpEq_trans
      (zpScale_congr prime' (zpAdd_congr leftZero rightOne))
      (zpScale_congr prime' (zpZero_add_left p prime x.value))⟩

theorem qpZero_add_right (p : BHist) (prime : NatPrime p) (x : QpInt p) :
    QpEq (qpAdd x (qpZero p prime)) x := by
  exact QpEq_trans (qpAdd_comm x (qpZero p prime))
    (qpZero_add_left p prime x)

theorem qpZero_prime_irrel {p : BHist} (prime prime' : NatPrime p) :
    QpEq (qpZero p prime) (qpZero p prime') := by
  apply QpEq_of_shift_value
  · rfl
  · exact zpZero_prime_irrel prime prime'

theorem qpAdd_neg_left {p : BHist} (x : QpInt p) :
    QpEq (qpAdd (qpNeg x) x) (qpZero p x.value.prime) := by
  intro prime
  exact ⟨0, by
    rw [Nat.zero_add, Nat.zero_add]
    have scaleZeroLeft :
        ZpEq (zpScale p prime 0 (qpAdd (qpNeg x) x).value)
          (qpAdd (qpNeg x) x).value :=
      zpOne_mul_left p prime (qpAdd (qpNeg x) x).value
    have canon :
        ZpEq (qpAdd (qpNeg x) x).value
          (zpAdd p
            (zpScale p prime x.shift (zpNeg p x.value))
            (zpScale p prime x.shift x.value)) :=
      qpAdd_value_canonical prime (qpNeg x) x
    have folded :
        ZpEq
          (zpAdd p
            (zpScale p prime x.shift (zpNeg p x.value))
            (zpScale p prime x.shift x.value))
          (zpScale p prime x.shift (zpZero p x.value.prime)) :=
      ZpEq_trans
        (ZpEq_symm
          (zpScale_add_distrib p prime x.shift (zpNeg p x.value) x.value))
        (zpScale_congr prime (zpAdd_neg_left p x.value))
    have leftZero :
        ZpEq (zpScale p prime x.shift (zpZero p x.value.prime))
          (zpZero p x.value.prime) :=
      zpScale_zero p prime x.value.prime x.shift
    have rightZero :
        ZpEq (zpScale p prime (x.shift + x.shift) (qpZero p x.value.prime).value)
          (zpZero p x.value.prime) :=
      zpScale_zero p prime x.value.prime (x.shift + x.shift)
    exact ZpEq_trans scaleZeroLeft
      (ZpEq_trans canon
        (ZpEq_trans folded
          (ZpEq_trans leftZero (ZpEq_symm rightZero))))⟩

theorem qpAdd_neg_right {p : BHist} (x : QpInt p) :
    QpEq (qpAdd x (qpNeg x)) (qpZero p x.value.prime) := by
  exact QpEq_trans (qpAdd_comm x (qpNeg x)) (qpAdd_neg_left x)

theorem qpAdd_neg_left_prime {p : BHist} (prime : NatPrime p) (x : QpInt p) :
    QpEq (qpAdd (qpNeg x) x) (qpZero p prime) := by
  exact QpEq_trans (qpAdd_neg_left x) (qpZero_prime_irrel x.value.prime prime)

theorem qpAdd_neg_right_prime {p : BHist} (prime : NatPrime p) (x : QpInt p) :
    QpEq (qpAdd x (qpNeg x)) (qpZero p prime) := by
  exact QpEq_trans (qpAdd_neg_right x) (qpZero_prime_irrel x.value.prime prime)

theorem qpNeg_respects {p : BHist} {x y : QpInt p} :
    QpEq x y -> QpEq (qpNeg x) (qpNeg y) := by
  intro same
  have negXAddYZero : QpEq (qpAdd (qpNeg x) y) (qpZero p y.value.prime) := by
    have lift : QpEq (qpAdd (qpNeg x) x) (qpAdd (qpNeg x) y) :=
      qpAdd_respects (QpEq_refl (qpNeg x)) same
    exact QpEq_trans (QpEq_symm lift)
      (QpEq_trans (qpAdd_neg_left x) (qpZero_prime_irrel x.value.prime y.value.prime))
  have yAddNegYZero : QpEq (qpAdd y (qpNeg y)) (qpZero p y.value.prime) :=
    qpAdd_neg_right y
  exact QpEq_trans
    (QpEq_symm (qpZero_add_right p y.value.prime (qpNeg x)))
    (QpEq_trans
      (qpAdd_respects (QpEq_refl (qpNeg x)) (QpEq_symm yAddNegYZero))
      (QpEq_trans
        (QpEq_symm (qpAdd_assoc (qpNeg x) y (qpNeg y)))
        (QpEq_trans
          (qpAdd_respects negXAddYZero (QpEq_refl (qpNeg y)))
          (qpZero_add_left p y.value.prime (qpNeg y)))))

theorem qpMul_add_distrib {p : BHist} (x y z : QpInt p) :
    QpEq (qpMul x (qpAdd y z)) (qpAdd (qpMul x y) (qpMul x z)) := by
  let xy := zpMul p x.value y.value
  let xz := zpMul p x.value z.value
  let common : QpInt p :=
    { shift := x.shift + (y.shift + z.shift)
      value := zpAdd p (zpScale p x.value.prime z.shift xy)
        (zpScale p x.value.prime y.shift xz) }
  have leftCommon : QpEq (qpMul x (qpAdd y z)) common := by
    apply QpEq_of_shift_value
    · rfl
    · unfold qpMul common xy xz
      dsimp
      have addCanon :
          ZpEq (qpAdd y z).value
            (zpAdd p (zpScale p x.value.prime z.shift y.value)
              (zpScale p x.value.prime y.shift z.value)) :=
        qpAdd_value_canonical x.value.prime y z
      have mulCanon :
          ZpEq (zpMul p x.value (qpAdd y z).value)
            (zpMul p x.value
              (zpAdd p (zpScale p x.value.prime z.shift y.value)
                (zpScale p x.value.prime y.shift z.value))) :=
        zpMul_right_congr addCanon
      have distrib :
          ZpEq
            (zpMul p x.value
              (zpAdd p (zpScale p x.value.prime z.shift y.value)
                (zpScale p x.value.prime y.shift z.value)))
            (zpAdd p
              (zpMul p x.value (zpScale p x.value.prime z.shift y.value))
              (zpMul p x.value (zpScale p x.value.prime y.shift z.value))) :=
        zpMul_add_distrib p x.value
          (zpScale p x.value.prime z.shift y.value)
          (zpScale p x.value.prime y.shift z.value)
      have terms :
          ZpEq
            (zpAdd p
              (zpMul p x.value (zpScale p x.value.prime z.shift y.value))
              (zpMul p x.value (zpScale p x.value.prime y.shift z.value)))
            (zpAdd p (zpScale p x.value.prime z.shift (zpMul p x.value y.value))
              (zpScale p x.value.prime y.shift (zpMul p x.value z.value))) :=
        zpAdd_congr
          (zpMul_scale_right p x.value.prime z.shift x.value y.value)
          (zpMul_scale_right p x.value.prime y.shift x.value z.value)
      exact ZpEq_trans mulCanon (ZpEq_trans distrib terms)
  have rightToRescale :
      QpEq (qpAdd (qpMul x y) (qpMul x z)) (qpRescale x.shift common) := by
    apply QpEq_of_shift_value
    · unfold qpAdd qpMul qpRescale common
      dsimp
      exact qpNat_right_distrib_shift x.shift y.shift z.shift
    · unfold qpAdd qpMul qpRescale common xy xz
      dsimp
      have rightCanon :
          ZpEq
            (zpAdd p
              (zpMul p (pPowZp p (zpMul p x.value y.value).prime (x.shift + z.shift))
                (zpMul p x.value y.value))
              (zpMul p (pPowZp p (zpMul p x.value y.value).prime (x.shift + y.shift))
                (zpMul p x.value z.value)))
            (zpAdd p
              (zpScale p x.value.prime (x.shift + z.shift) (zpMul p x.value y.value))
              (zpScale p x.value.prime (x.shift + y.shift) (zpMul p x.value z.value))) := by
        exact zpAdd_congr
          (by
            unfold zpScale
            exact zpMul_left_congr
              (pPowZp_prime_irrel (zpMul p x.value y.value).prime x.value.prime
                (x.shift + z.shift)))
          (by
            unfold zpScale
            exact zpMul_left_congr
              (pPowZp_prime_irrel (zpMul p x.value y.value).prime x.value.prime
                (x.shift + y.shift)))
      have scaledCommon :
          ZpEq
            (zpScale p (zpAdd p (zpScale p x.value.prime z.shift (zpMul p x.value y.value))
              (zpScale p x.value.prime y.shift (zpMul p x.value z.value))).prime x.shift
              (zpAdd p (zpScale p x.value.prime z.shift (zpMul p x.value y.value))
                (zpScale p x.value.prime y.shift (zpMul p x.value z.value))))
            (zpAdd p
              (zpScale p x.value.prime (x.shift + z.shift) (zpMul p x.value y.value))
              (zpScale p x.value.prime (x.shift + y.shift) (zpMul p x.value z.value))) := by
        have primeSwap :
            ZpEq
              (zpScale p (zpAdd p (zpScale p x.value.prime z.shift (zpMul p x.value y.value))
                (zpScale p x.value.prime y.shift (zpMul p x.value z.value))).prime x.shift
                (zpAdd p (zpScale p x.value.prime z.shift (zpMul p x.value y.value))
                  (zpScale p x.value.prime y.shift (zpMul p x.value z.value))))
              (zpScale p x.value.prime x.shift
                (zpAdd p (zpScale p x.value.prime z.shift (zpMul p x.value y.value))
                  (zpScale p x.value.prime y.shift (zpMul p x.value z.value)))) :=
          zpScale_prime_irrel
            (zpAdd p (zpScale p x.value.prime z.shift (zpMul p x.value y.value))
              (zpScale p x.value.prime y.shift (zpMul p x.value z.value))).prime
            x.value.prime x.shift
            (zpAdd p (zpScale p x.value.prime z.shift (zpMul p x.value y.value))
              (zpScale p x.value.prime y.shift (zpMul p x.value z.value)))
        have distribScale :
            ZpEq
              (zpScale p x.value.prime x.shift
                (zpAdd p (zpScale p x.value.prime z.shift (zpMul p x.value y.value))
                  (zpScale p x.value.prime y.shift (zpMul p x.value z.value))))
              (zpAdd p
                (zpScale p x.value.prime x.shift
                  (zpScale p x.value.prime z.shift (zpMul p x.value y.value)))
                (zpScale p x.value.prime x.shift
                  (zpScale p x.value.prime y.shift (zpMul p x.value z.value)))) :=
          zpScale_add_distrib p x.value.prime x.shift
            (zpScale p x.value.prime z.shift (zpMul p x.value y.value))
            (zpScale p x.value.prime y.shift (zpMul p x.value z.value))
        have reindex :
            ZpEq
              (zpAdd p
                (zpScale p x.value.prime x.shift
                  (zpScale p x.value.prime z.shift (zpMul p x.value y.value)))
                (zpScale p x.value.prime x.shift
                  (zpScale p x.value.prime y.shift (zpMul p x.value z.value))))
              (zpAdd p
                (zpScale p x.value.prime (x.shift + z.shift) (zpMul p x.value y.value))
                (zpScale p x.value.prime (x.shift + y.shift) (zpMul p x.value z.value))) :=
          zpAdd_congr
            (zpScale_scale p x.value.prime x.shift z.shift (zpMul p x.value y.value))
            (zpScale_scale p x.value.prime x.shift y.shift (zpMul p x.value z.value))
        exact ZpEq_trans primeSwap (ZpEq_trans distribScale reindex)
      exact ZpEq_trans rightCanon (ZpEq_symm scaledCommon)
  exact QpEq_trans leftCommon
    (QpEq_symm (QpEq_trans rightToRescale (qpRescale_eq x.shift common)))

theorem qpMul_add_distrib_right {p : BHist} (x y z : QpInt p) :
    QpEq (qpMul (qpAdd x y) z) (qpAdd (qpMul x z) (qpMul y z)) := by
  exact QpEq_trans
    (qpMul_comm (qpAdd x y) z)
    (QpEq_trans
      (qpMul_add_distrib z x y)
      (qpAdd_respects (qpMul_comm z x) (qpMul_comm z y)))

structure QpLocalizationCore (p : BHist) where
  carrier : Type
  eqv : carrier -> carrier -> Prop
  eq_refl : ∀ x : carrier, eqv x x
  eq_symm : ∀ {x y : carrier}, eqv x y -> eqv y x
  eq_trans : ∀ {x y z : carrier}, eqv x y -> eqv y z -> eqv x z
  zero : NatPrime p -> carrier
  one : NatPrime p -> carrier
  add : carrier -> carrier -> carrier
  mul : carrier -> carrier -> carrier
  neg : carrier -> carrier
  add_respects : ∀ {x x' y y' : carrier}, eqv x x' -> eqv y y' ->
    eqv (add x y) (add x' y')
  mul_respects : ∀ {x x' y y' : carrier}, eqv x x' -> eqv y y' ->
    eqv (mul x y) (mul x' y')
  neg_respects : ∀ {x y : carrier}, eqv x y -> eqv (neg x) (neg y)
  add_comm : ∀ x y : carrier, eqv (add x y) (add y x)
  add_assoc : ∀ x y z : carrier, eqv (add (add x y) z) (add x (add y z))
  zero_add : ∀ (prime : NatPrime p) (x : carrier), eqv (add (zero prime) x) x
  add_zero : ∀ (prime : NatPrime p) (x : carrier), eqv (add x (zero prime)) x
  neg_add : ∀ (prime : NatPrime p) (x : carrier), eqv (add (neg x) x) (zero prime)
  add_neg : ∀ (prime : NatPrime p) (x : carrier), eqv (add x (neg x)) (zero prime)
  mul_comm : ∀ x y : carrier, eqv (mul x y) (mul y x)
  mul_assoc : ∀ x y z : carrier, eqv (mul (mul x y) z) (mul x (mul y z))
  one_mul : ∀ (prime : NatPrime p) (x : carrier), eqv (mul (one prime) x) x
  mul_one : ∀ (prime : NatPrime p) (x : carrier), eqv (mul x (one prime)) x
  left_distrib : ∀ x y z : carrier, eqv (mul x (add y z)) (add (mul x y) (mul x z))
  right_distrib : ∀ x y z : carrier, eqv (mul (add x y) z) (add (mul x z) (mul y z))

def QpInt_localization_core (p : BHist) : QpLocalizationCore p :=
  { carrier := QpInt p
    eqv := QpEq
    eq_refl := QpEq_refl
    eq_symm := QpEq_symm
    eq_trans := QpEq_trans
    zero := qpZero p
    one := qpOne p
    add := qpAdd
    mul := qpMul
    neg := qpNeg
    add_respects := qpAdd_respects
    mul_respects := qpMul_respects
    neg_respects := qpNeg_respects
    add_comm := qpAdd_comm
    add_assoc := qpAdd_assoc
    zero_add := qpZero_add_left p
    add_zero := qpZero_add_right p
    neg_add := qpAdd_neg_left_prime
    add_neg := qpAdd_neg_right_prime
    mul_comm := qpMul_comm
    mul_assoc := qpMul_assoc
    one_mul := qpOne_mul_left p
    mul_one := qpOne_mul_right p
    left_distrib := qpMul_add_distrib
    right_distrib := qpMul_add_distrib_right }

def QpValIndex (valueShift : BHist) (denomShift : Nat) : BHist × BHist :=
  (valueShift, zpuNatToUnary denomShift)

def QpValOfIntPair (p : BHist) (valueShift : BHist) (denomShift : Nat)
    (z : BEDC.FKernel.Mark.BMark × BHist) : Prop :=
  IsPadicValInt p z valueShift ∧
    IntPairCarrier (QpValIndex valueShift denomShift).1
      (QpValIndex valueShift denomShift).2

theorem QpValOfIntPair_index_carrier {p valueShift : BHist} {denomShift : Nat}
    {z : BEDC.FKernel.Mark.BMark × BHist} :
    QpValOfIntPair p valueShift denomShift z ->
      IntPairCarrier (QpValIndex valueShift denomShift).1
        (QpValIndex valueShift denomShift).2 := by
  intro val
  exact val.right

end BEDC.Derived.PadicUp
