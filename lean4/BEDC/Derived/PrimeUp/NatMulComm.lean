import BEDC.Derived.PrimeUp.NatMulCases
import BEDC.FKernel.ExternalBinary

namespace BEDC.Derived.PrimeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary

private theorem unary_hsame_of_bwordLength_eq {h k : BHist} :
    UnaryHistory h -> UnaryHistory k -> bwordLength h = bwordLength k -> hsame h k := by
  intro uh
  induction h generalizing k with
  | Empty =>
      intro uk lengthEq
      cases k with
      | Empty =>
          rfl
      | e0 k =>
          cases uk
      | e1 k =>
          cases lengthEq
  | e0 h _ih =>
      cases uh
  | e1 h ih =>
      intro uk lengthEq
      cases k with
      | Empty =>
          cases lengthEq
      | e0 k =>
          cases uk
      | e1 k =>
          exact hsame_e1_congr (ih uh uk (Nat.succ.inj lengthEq))

private theorem nat_mul_assoc_pure (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      calc
        (a * b) * Nat.succ c = (a * b) * c + a * b := Nat.mul_succ (a * b) c
        _ = a * (b * c) + a * b := congrArg (fun x => x + a * b) ih
        _ = a * (b * c + b) := (Nat.mul_add a (b * c) b).symm
        _ = a * (b * Nat.succ c) := congrArg (fun x => a * x) (Nat.mul_succ b c).symm

theorem NatMul_bwordLength {d q n : BHist} :
    NatMul d q n -> bwordLength n = bwordLength d * bwordLength q := by
  intro mul
  induction mul with
  | zero _hd =>
      exact (Nat.mul_zero (bwordLength d)).symm
  | succ previous step ih =>
      calc
        bwordLength _ = bwordLength (BEDC.FKernel.Cont.append _ d) := congrArg bwordLength step
        _ = bwordLength _ + bwordLength d := bwordLength_append _ d
        _ = bwordLength d * bwordLength _ + bwordLength d :=
          congrArg (fun x => x + bwordLength d) ih
        _ = bwordLength d * Nat.succ (bwordLength _) :=
          (Nat.mul_succ (bwordLength d) (bwordLength _)).symm

theorem NatMul_comm_hsame {d q n m : BHist} :
    UnaryHistory d -> UnaryHistory q -> NatMul d q n -> NatMul q d m -> hsame n m := by
  intro hd hq left right
  have unaryN : UnaryHistory n := NatMul_result_unary hd left
  have unaryM : UnaryHistory m := NatMul_result_unary hq right
  apply unary_hsame_of_bwordLength_eq unaryN unaryM
  calc
    bwordLength n = bwordLength d * bwordLength q := NatMul_bwordLength left
    _ = bwordLength q * bwordLength d := Nat.mul_comm (bwordLength d) (bwordLength q)
    _ = bwordLength m := (NatMul_bwordLength right).symm

theorem NatMul_assoc_hsame {a b c ab left bc right : BHist} :
    UnaryHistory a -> UnaryHistory b -> UnaryHistory c -> NatMul a b ab ->
      NatMul ab c left -> NatMul b c bc -> NatMul a bc right -> hsame left right := by
  intro ha _hb _hc mulAB mulLeft mulBC mulRight
  have unaryAB : UnaryHistory ab := NatMul_result_unary ha mulAB
  have unaryBC : UnaryHistory bc := NatMul_right_unary mulRight
  have unaryLeft : UnaryHistory left := NatMul_result_unary unaryAB mulLeft
  have unaryRight : UnaryHistory right := NatMul_result_unary ha mulRight
  apply unary_hsame_of_bwordLength_eq unaryLeft unaryRight
  calc
    bwordLength left = bwordLength ab * bwordLength c := NatMul_bwordLength mulLeft
    _ = (bwordLength a * bwordLength b) * bwordLength c :=
      congrArg (fun x => x * bwordLength c) (NatMul_bwordLength mulAB)
    _ = bwordLength a * (bwordLength b * bwordLength c) :=
      nat_mul_assoc_pure (bwordLength a) (bwordLength b) (bwordLength c)
    _ = bwordLength a * bwordLength bc :=
      congrArg (fun x => bwordLength a * x) (NatMul_bwordLength mulBC).symm
    _ = bwordLength right := (NatMul_bwordLength mulRight).symm

theorem NatMul_unary_mulup_certificate :
    (∀ {d q : BHist}, UnaryHistory d -> UnaryHistory q ->
      ∃ n : BHist, UnaryHistory n ∧ NatMul d q n) ∧
    (∀ {d q n : BHist}, UnaryHistory d -> NatMul d q n -> UnaryHistory n) ∧
    (∀ {d q n m : BHist}, UnaryHistory d -> NatMul d q n -> NatMul d q m ->
      hsame n m) ∧
    (∀ {q n : BHist}, UnaryHistory q -> NatMul (BHist.e1 BHist.Empty) q n ->
      hsame n q) ∧
    (∀ {d n : BHist}, NatMul d (BHist.e1 BHist.Empty) n -> hsame n d) ∧
    (∀ {d q n m : BHist}, UnaryHistory d -> UnaryHistory q -> NatMul d q n ->
      NatMul q d m -> hsame n m) ∧
    (∀ {a b c ab left bc right : BHist},
      UnaryHistory a -> UnaryHistory b -> UnaryHistory c -> NatMul a b ab ->
        NatMul ab c left -> NatMul b c bc -> NatMul a bc right -> hsame left right) := by
  constructor
  · intro d q dUnary qUnary
    exact NatMul_total dUnary qUnary
  · constructor
    · intro d q n dUnary mul
      exact NatMul_result_unary dUnary mul
    · constructor
      · intro d q n m dUnary left right
        exact NatMul_functional dUnary left right
      · constructor
        · intro q n qUnary mul
          exact NatMul_unit_left_hsame qUnary mul
        · constructor
          · intro d n mul
            exact NatMul_unit_right_hsame mul
          · constructor
            · intro d q n m dUnary qUnary left right
              exact NatMul_comm_hsame dUnary qUnary left right
            · intro a b c ab left bc right aUnary bUnary cUnary mulAB mulLeft mulBC mulRight
              exact NatMul_assoc_hsame aUnary bUnary cUnary mulAB mulLeft mulBC mulRight

end BEDC.Derived.PrimeUp
