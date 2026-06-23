import BEDC.Derived.PadicUp.IntegerTower

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp

theorem natMulFn_append_left_distrib_hsame {a b c : BHist} :
    UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
      hsame (natMulFn a (BEDC.FKernel.Cont.append b c))
        (BEDC.FKernel.Cont.append (natMulFn a b) (natMulFn a c)) := by
  intro aUnary bUnary cUnary
  induction c with
  | Empty =>
      change hsame (natMulFn a b)
        (BEDC.FKernel.Cont.append (natMulFn a b) BHist.Empty)
      exact hsame_symm (append_empty_right (natMulFn a b))
  | e0 _ =>
      cases cUnary
  | e1 ctail ih =>
      have tailUnary : UnaryHistory ctail := unary_e1_inversion cUnary
      change hsame
        (BEDC.FKernel.Cont.append (natMulFn a (BEDC.FKernel.Cont.append b ctail)) a)
        (BEDC.FKernel.Cont.append (natMulFn a b)
          (BEDC.FKernel.Cont.append (natMulFn a ctail) a))
      have ihSame :
          hsame (natMulFn a (BEDC.FKernel.Cont.append b ctail))
            (BEDC.FKernel.Cont.append (natMulFn a b) (natMulFn a ctail)) :=
        ih tailUnary
      exact hsame_trans
        (congrArg (fun h => BEDC.FKernel.Cont.append h a) ihSame)
        (BEDC.FKernel.Cont.append_assoc (natMulFn a b) (natMulFn a ctail) a)

theorem natMulFn_append_right_distrib_hsame {a b c : BHist} :
    UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
      hsame (natMulFn (BEDC.FKernel.Cont.append a b) c)
        (BEDC.FKernel.Cont.append (natMulFn a c) (natMulFn b c)) := by
  intro aUnary bUnary cUnary
  have abUnary : UnaryHistory (BEDC.FKernel.Cont.append a b) :=
    unary_append_closed aUnary bUnary
  have distributed :
      NatAdd (natMulFn a c) (natMulFn b c)
        (natMulFn (BEDC.FKernel.Cont.append a b) c) :=
    NatMul_cont_right_distrib aUnary bUnary cUnary (cont_intro rfl)
      (natMulFn_rel aUnary cUnary) (natMulFn_rel bUnary cUnary)
      (natMulFn_rel abUnary cUnary)
  exact distributed.right.right

theorem natModFn_mul_add_distrib {M a b c : BHist} :
    UnaryHistory M -> (hsame M BHist.Empty -> False) ->
      UnaryHistory a -> UnaryHistory b -> UnaryHistory c ->
        hsame
          (natModFn M (natMulFn a (BEDC.FKernel.Cont.append b c)))
          (natModFn M
            (BEDC.FKernel.Cont.append (natMulFn a b) (natMulFn a c))) := by
  intro MUnary MNonempty aUnary bUnary cUnary
  exact natModFn_hsame_arg_transport (M := M)
    (natMulFn_append_left_distrib_hsame aUnary bUnary cUnary)

theorem zpMul_add_distrib (p : BHist) (x y z : ZpInt p) :
    ZpEq (zpMul p x (zpAdd p y z))
      (zpAdd p (zpMul p x y) (zpMul p x z)) := by
  intro N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (natMulFn (x.trunc N NUnary).val
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val))))
    (natModFn (pPowCanon p N)
      (BEDC.FKernel.Cont.append
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val))))
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime NUnary
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have yUnary : UnaryHistory (y.trunc N NUnary).val :=
    BoundedNat_unary MUnary (y.trunc N NUnary)
  have zUnary : UnaryHistory (z.trunc N NUnary).val :=
    BoundedNat_unary MUnary (z.trunc N NUnary)
  have yzUnary :
      UnaryHistory (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val) :=
    unary_append_closed yUnary zUnary
  have xyUnary : UnaryHistory (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val) :=
    natMulFn_unary xUnary yUnary
  have xzUnary : UnaryHistory (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val) :=
    natMulFn_unary xUnary zUnary
  have leftToRaw :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val
            (natModFn (pPowCanon p N)
              (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val))))
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val
            (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val))) :=
    natModFn_mul_right_reduce_same_mod MUnary MNonempty xUnary yzUnary
  have rawDistrib :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val
            (BEDC.FKernel.Cont.append (y.trunc N NUnary).val (z.trunc N NUnary).val)))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val))) :=
    natModFn_mul_add_distrib MUnary MNonempty xUnary yUnary zUnary
  have rawToRight :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val)))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N)
              (natMulFn (x.trunc N NUnary).val (y.trunc N NUnary).val))
            (natModFn (pPowCanon p N)
              (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val)))) := by
    exact mod_add_compat MUnary MNonempty xyUnary xzUnary
  exact hsame_trans leftToRaw (hsame_trans rawDistrib rawToRight)

theorem zpMul_add_distrib_right (p : BHist) (x y z : ZpInt p) :
    ZpEq (zpMul p (zpAdd p x y) z)
      (zpAdd p (zpMul p x z) (zpMul p y z)) := by
  intro N NUnary
  change hsame
    (natModFn (pPowCanon p N)
      (natMulFn
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val))
        (z.trunc N NUnary).val))
    (natModFn (pPowCanon p N)
      (BEDC.FKernel.Cont.append
        (natModFn (pPowCanon p N)
          (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val))))
  have MUnary : UnaryHistory (pPowCanon p N) := pPowCanon_unary p N
  have MNonempty : hsame (pPowCanon p N) BHist.Empty -> False :=
    pPowCanon_nonempty_of_prime x.prime NUnary
  have xUnary : UnaryHistory (x.trunc N NUnary).val :=
    BoundedNat_unary MUnary (x.trunc N NUnary)
  have yUnary : UnaryHistory (y.trunc N NUnary).val :=
    BoundedNat_unary MUnary (y.trunc N NUnary)
  have zUnary : UnaryHistory (z.trunc N NUnary).val :=
    BoundedNat_unary MUnary (z.trunc N NUnary)
  have xyRawUnary :
      UnaryHistory (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val) :=
    unary_append_closed xUnary yUnary
  have xzUnary : UnaryHistory (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val) :=
    natMulFn_unary xUnary zUnary
  have yzUnary : UnaryHistory (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val) :=
    natMulFn_unary yUnary zUnary
  have leftToRaw :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn
            (natModFn (pPowCanon p N)
              (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val))
            (z.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (natMulFn
            (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (z.trunc N NUnary).val)) :=
    natModFn_mul_left_reduce_same_mod MUnary MNonempty xyRawUnary zUnary
  have rawDistrib :
      hsame
        (natModFn (pPowCanon p N)
          (natMulFn
            (BEDC.FKernel.Cont.append (x.trunc N NUnary).val (y.trunc N NUnary).val)
            (z.trunc N NUnary).val))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val)
            (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val))) :=
    natModFn_hsame_arg_transport (M := pPowCanon p N)
      (natMulFn_append_right_distrib_hsame xUnary yUnary zUnary)
  have rawToRight :
      hsame
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val)
            (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val)))
        (natModFn (pPowCanon p N)
          (BEDC.FKernel.Cont.append
            (natModFn (pPowCanon p N)
              (natMulFn (x.trunc N NUnary).val (z.trunc N NUnary).val))
            (natModFn (pPowCanon p N)
              (natMulFn (y.trunc N NUnary).val (z.trunc N NUnary).val)))) := by
    exact mod_add_compat MUnary MNonempty xzUnary yzUnary
  exact hsame_trans leftToRaw (hsame_trans rawDistrib rawToRight)

structure ZpIntDistribSemiringLaws (p : BHist) where
  add_comm : ∀ x y : ZpInt p, ZpEq (zpAdd p x y) (zpAdd p y x)
  add_assoc : ∀ x y z : ZpInt p,
    ZpEq (zpAdd p (zpAdd p x y) z) (zpAdd p x (zpAdd p y z))
  zero_add : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpAdd p (zpZero p prime) x) x
  add_zero : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpAdd p x (zpZero p prime)) x
  mul_comm : ∀ x y : ZpInt p, ZpEq (zpMul p x y) (zpMul p y x)
  mul_assoc : ∀ x y z : ZpInt p,
    ZpEq (zpMul p (zpMul p x y) z) (zpMul p x (zpMul p y z))
  one_mul : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpMul p (zpOne p prime) x) x
  mul_one : ∀ (prime : NatPrime p) (x : ZpInt p),
    ZpEq (zpMul p x (zpOne p prime)) x
  left_distrib : ∀ x y z : ZpInt p,
    ZpEq (zpMul p x (zpAdd p y z))
      (zpAdd p (zpMul p x y) (zpMul p x z))
  right_distrib : ∀ x y z : ZpInt p,
    ZpEq (zpMul p (zpAdd p x y) z)
      (zpAdd p (zpMul p x z) (zpMul p y z))

def ZpInt_distrib_semiring_laws (p : BHist) : ZpIntDistribSemiringLaws p :=
  { add_comm := zpAdd_comm p
    add_assoc := zpAdd_assoc p
    zero_add := zpZero_add_left p
    add_zero := zpZero_add_right p
    mul_comm := zpMul_comm p
    mul_assoc := zpMul_assoc p
    one_mul := zpOne_mul_left p
    mul_one := zpOne_mul_right p
    left_distrib := zpMul_add_distrib p
    right_distrib := zpMul_add_distrib_right p }

end BEDC.Derived.PadicUp
