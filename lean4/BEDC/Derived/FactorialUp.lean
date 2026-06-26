import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.PrimeUp.NatMulComm
import BEDC.Derived.PrimeUp.NatMulTransport
import BEDC.Derived.IntUp.Arithmetic

namespace BEDC.Derived.FactorialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary (bwordLength)
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.IntUp (natMulFn natMulFn_unary natMulFn_rel)

abbrev NatOne : BHist := BHist.e1 BHist.Empty

inductive NatFactorial : BHist -> BHist -> Prop where
  | zero : NatFactorial BHist.Empty NatOne
  | succ {n f r : BHist} :
      NatFactorial n f -> NatMul (BHist.e1 n) f r -> NatFactorial (BHist.e1 n) r

namespace NatFactorial

theorem factorial_succ {n f r : BHist} :
    NatFactorial n f -> NatMul (BHist.e1 n) f r -> NatFactorial (BHist.e1 n) r := by
  intro factorial product
  exact NatFactorial.succ factorial product

theorem index_unary {n f : BHist} :
    NatFactorial n f -> UnaryHistory n := by
  intro factorial
  induction factorial with
  | zero =>
      exact unary_empty
  | succ _factorial _product ih =>
      exact unary_e1_closed ih

theorem result_unary {n f : BHist} :
    NatFactorial n f -> UnaryHistory f := by
  intro factorial
  induction factorial with
  | zero =>
      exact unary_e1_closed unary_empty
  | succ _factorial product _ih =>
      exact NatMul_result_unary (NatMul_left_unary product) product

theorem factorial_pos {n f : BHist} :
    NatFactorial n f -> hsame f BHist.Empty -> False := by
  intro factorial emptyResult
  induction factorial with
  | zero =>
      exact not_hsame_e1_empty emptyResult
  | succ _factorial product ih =>
      exact NatMul_nonempty_factors_result_not_empty not_hsame_e1_empty ih product emptyResult

theorem total {n : BHist} :
    UnaryHistory n -> ∃ f : BHist, UnaryHistory f ∧ NatFactorial n f := by
  intro nUnary
  induction n with
  | Empty =>
      exact ⟨NatOne, unary_e1_closed unary_empty, NatFactorial.zero⟩
  | e0 _n =>
      cases nUnary
  | e1 n ih =>
      have previous := ih nUnary
      cases previous with
      | intro f fData =>
          have multiplierUnary : UnaryHistory (BHist.e1 n) := unary_e1_closed nUnary
          have product := NatMul_total multiplierUnary fData.left
          cases product with
          | intro r rData =>
              exact ⟨r, rData.left, NatFactorial.succ fData.right rData.right⟩

theorem functional {n f g : BHist} :
    NatFactorial n f -> NatFactorial n g -> hsame f g := by
  intro left
  induction left generalizing g with
  | zero =>
      intro right
      cases right
      rfl
  | succ leftPrev leftProduct ih =>
      intro right
      cases right with
      | succ rightPrev rightProduct =>
          have samePrev : hsame _ _ := ih rightPrev
          have shifted :=
            NatMul_multiplicand_hsame_transport (hsame_refl _) leftProduct
          have shiftedProduct :=
            NatMul_multiplier_hsame_transport shifted.right samePrev
          exact NatMul_functional shifted.left shiftedProduct.right rightProduct

end NatFactorial

def natFactorialFn : BHist -> BHist
  | BHist.Empty => NatOne
  | BHist.e0 _ => BHist.Empty
  | BHist.e1 n => natMulFn (BHist.e1 n) (natFactorialFn n)

theorem natFactorialFn_rel {n : BHist} :
    UnaryHistory n -> NatFactorial n (natFactorialFn n) := by
  intro nUnary
  induction n with
  | Empty =>
      exact NatFactorial.zero
  | e0 _n =>
      cases nUnary
  | e1 n ih =>
      have prevRel := ih nUnary
      have prevUnary := NatFactorial.result_unary prevRel
      exact NatFactorial.succ prevRel
        (natMulFn_rel (unary_e1_closed nUnary) prevUnary)

theorem natFactorialFn_unary {n : BHist} :
    UnaryHistory n -> UnaryHistory (natFactorialFn n) := by
  intro nUnary
  exact NatFactorial.result_unary (natFactorialFn_rel nUnary)

theorem natFactorialFn_spec {n f : BHist} :
    UnaryHistory n -> NatFactorial n f -> hsame (natFactorialFn n) f := by
  intro nUnary factorial
  exact NatFactorial.functional (natFactorialFn_rel nUnary) factorial

theorem natFactorialFn_succ {n : BHist} :
    UnaryHistory n ->
      NatMul (BHist.e1 n) (natFactorialFn n) (natFactorialFn (BHist.e1 n)) := by
  intro nUnary
  change NatMul (BHist.e1 n) (natFactorialFn n)
    (natMulFn (BHist.e1 n) (natFactorialFn n))
  exact natMulFn_rel (unary_e1_closed nUnary) (natFactorialFn_unary nUnary)

private def chooseCount : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | Nat.succ n, Nat.succ k => chooseCount n k + chooseCount n (Nat.succ k)

private theorem chooseCount_zero_right (n : Nat) : chooseCount n 0 = 1 := by
  cases n <;> rfl

private theorem chooseCount_pascal (n k : Nat) :
    chooseCount (Nat.succ n) (Nat.succ k) =
      chooseCount n k + chooseCount n (Nat.succ k) := by
  rfl

def natChooseFn (n k : BHist) : BHist :=
  BEDC.Derived.IntUp.natToUnary (chooseCount (bwordLength n) (bwordLength k))

theorem natChooseFn_boundary_left {n : BHist} :
    natChooseFn (BHist.e1 n) BHist.Empty = NatOne := by
  unfold natChooseFn
  cases bwordLength n <;> rfl

theorem chooseCount_self_and_above :
    ∀ n : Nat, chooseCount n n = 1 ∧
      ∀ extra : Nat, chooseCount n (Nat.succ (n + extra)) = 0 := by
  intro n
  induction n with
  | zero =>
      constructor
      · rfl
      · intro extra
        rfl
  | succ n ih =>
      constructor
      · change chooseCount n n + chooseCount n (Nat.succ n) = 1
        rw [ih.left, ih.right 0]
      · intro extra
        rw [Nat.succ_add]
        change chooseCount n (Nat.succ (n + extra)) +
          chooseCount n (Nat.succ (Nat.succ (n + extra))) = 0
        rw [ih.right extra]
        have shifted : n + Nat.succ extra = Nat.succ (n + extra) := Nat.add_succ n extra
        rw [← shifted]
        rw [ih.right (Nat.succ extra)]

theorem chooseCount_self (n : Nat) : chooseCount n n = 1 :=
  (chooseCount_self_and_above n).left

private theorem chooseCount_above (n extra : Nat) :
    chooseCount n (Nat.succ (n + extra)) = 0 :=
  (chooseCount_self_and_above n).right extra

theorem natChooseFn_boundary_self {n : BHist} :
    natChooseFn n n = NatOne := by
  unfold natChooseFn
  rw [chooseCount_self (bwordLength n)]
  rfl

theorem natChooseFn_zero : natChooseFn BHist.Empty BHist.Empty = NatOne := by
  exact natChooseFn_boundary_self (n := BHist.Empty)

theorem natChooseFn_unary_result {n k : BHist} :
    UnaryHistory (natChooseFn n k) := by
  unfold natChooseFn
  exact BEDC.Derived.IntUp.natToUnary_unary _

inductive NatBinom : BHist -> BHist -> BHist -> Prop where
  | left {l : BHist} : UnaryHistory l -> NatBinom BHist.Empty l NatOne
  | right {k : BHist} : UnaryHistory k -> NatBinom k BHist.Empty NatOne
  | step {k l a b s : BHist} :
      NatBinom k (BHist.e1 l) a -> NatBinom (BHist.e1 k) l b ->
        NatAdd a b s -> NatBinom (BHist.e1 k) (BHist.e1 l) s

namespace NatBinom

theorem index_unary {k l c : BHist} :
    NatBinom k l c -> UnaryHistory k ∧ UnaryHistory l := by
  intro binom
  induction binom with
  | left lUnary =>
      exact ⟨unary_empty, lUnary⟩
  | right kUnary =>
      exact ⟨kUnary, unary_empty⟩
  | step _left _right _add ihLeft ihRight =>
      exact ⟨unary_e1_closed ihLeft.left, unary_e1_closed ihRight.right⟩

theorem result_unary {k l c : BHist} :
    NatBinom k l c -> UnaryHistory c := by
  intro binom
  induction binom with
  | left _lUnary =>
      exact unary_e1_closed unary_empty
  | right _kUnary =>
      exact unary_e1_closed unary_empty
  | step _left _right add _ihLeft _ihRight =>
      exact NatAdd_result_unary add

theorem hsame_transport {k l c k' l' c' : BHist} :
    NatBinom k l c -> hsame k k' -> hsame l l' -> hsame c c' ->
      NatBinom k' l' c' := by
  intro binom sameK sameL sameC
  cases sameK
  cases sameL
  cases sameC
  exact binom

theorem symm {k l c : BHist} :
    NatBinom k l c -> NatBinom l k c := by
  intro binom
  induction binom with
  | left lUnary =>
      exact NatBinom.right lUnary
  | right kUnary =>
      exact NatBinom.left kUnary
  | step left right add ihLeft ihRight =>
      have aUnary : UnaryHistory _ := result_unary left
      have bUnary : UnaryHistory _ := result_unary right
      have addCanonical : NatAdd _ _ (append _ _) := NatAdd_append_self bUnary aUnary
      have sameSum : hsame _ (append _ _) := NatAdd_comm_hsame add addCanonical
      have addBA : NatAdd _ _ _ :=
        ⟨bUnary, aUnary, cont_result_hsame_transport (cont_intro rfl) (hsame_symm sameSum)⟩
      exact NatBinom.step ihRight ihLeft addBA

end NatBinom

def NatChooseComplementary (k l n : BHist) : Prop :=
  UnaryHistory k ∧ UnaryHistory l ∧ Cont k l n

def NatChoose (n k c : BHist) : Prop :=
  ∃ l : BHist, NatChooseComplementary k l n ∧ NatBinom k l c

namespace NatChoose

abbrev Complementary := NatChooseComplementary

theorem complementary_comm {n k l : BHist} :
    Complementary k l n -> Complementary l k n := by
  intro comp
  exact ⟨comp.right.left, comp.left,
    cont_intro (comp.right.right.trans (unary_append_comm comp.right.left comp.left).symm)⟩

theorem index_unary {n k c : BHist} :
    NatChoose n k c -> UnaryHistory n ∧ UnaryHistory k := by
  intro choose
  cases choose with
  | intro l data =>
      exact ⟨unary_cont_closed data.left.left data.left.right.left data.left.right.right,
        data.left.left⟩

theorem result_unary {n k c : BHist} :
    NatChoose n k c -> UnaryHistory c := by
  intro choose
  cases choose with
  | intro _l data =>
      exact NatBinom.result_unary data.right

theorem left_boundary {n k c : BHist} :
    NatChoose n k c -> NatChoose (BHist.e1 n) BHist.Empty NatOne := by
  intro choose
  have nUnary : UnaryHistory n := (index_unary choose).left
  exact ⟨BHist.e1 n,
    ⟨unary_empty, unary_e1_closed nUnary, cont_left_unit (BHist.e1 n)⟩,
    NatBinom.left (unary_e1_closed nUnary)⟩

theorem right_boundary {n k c : BHist} :
    NatChoose n k c -> NatChoose n n NatOne := by
  intro choose
  have nUnary : UnaryHistory n := (index_unary choose).left
  exact ⟨BHist.Empty, ⟨nUnary, unary_empty, cont_right_unit n⟩,
    NatBinom.right nUnary⟩

theorem pascal_identity {n k left right sum : BHist} :
    NatChoose n k left -> NatChoose n (BHist.e1 k) right ->
      NatAdd left right sum -> NatChoose (BHist.e1 n) (BHist.e1 k) sum := by
  intro leftChoose rightChoose add
  cases leftChoose with
  | intro l leftData =>
      cases rightChoose with
      | intro r rightData =>
          have rUnary : UnaryHistory r := rightData.left.right.left
          have rightAsK : Cont k (BHist.e1 r) n :=
            cont_intro (rightData.left.right.right.trans
              (unary_append_e1_left (h := r) (k := k) rUnary))
          have sameComplement : hsame l (BHist.e1 r) :=
            cont_left_cancel leftData.left.right.right rightAsK
          have leftShifted : NatBinom k (BHist.e1 r) left :=
            NatBinom.hsame_transport leftData.right (hsame_refl k) sameComplement
              (hsame_refl left)
          have targetComp : Complementary (BHist.e1 k) (BHist.e1 r) (BHist.e1 n) :=
            ⟨unary_e1_closed leftData.left.left, unary_e1_closed rUnary,
              cont_intro (congrArg BHist.e1 rightData.left.right.right)⟩
          exact ⟨BHist.e1 r, targetComp, NatBinom.step leftShifted rightData.right add⟩

theorem pascal {n k left right sum : BHist} :
    NatChoose n k left -> NatChoose n (BHist.e1 k) right ->
      NatAdd left right sum -> NatChoose (BHist.e1 n) (BHist.e1 k) sum :=
  pascal_identity

theorem choose_symm {n k c l : BHist} :
    NatChoose n k c -> Complementary k l n -> NatChoose n l c := by
  intro choose comp
  cases choose with
  | intro l0 data =>
      have sameComplement : hsame l0 l :=
        cont_left_cancel data.left.right.right comp.right.right
      have symmetricBinom : NatBinom l0 k c := NatBinom.symm data.right
      have shiftedBinom : NatBinom l k c :=
        NatBinom.hsame_transport symmetricBinom sameComplement (hsame_refl k) (hsame_refl c)
      exact ⟨k, complementary_comm comp, shiftedBinom⟩

end NatChoose

theorem NatChoose_zero_rel :
    NatChoose BHist.Empty BHist.Empty (natChooseFn BHist.Empty BHist.Empty) := by
  change NatChoose BHist.Empty BHist.Empty NatOne
  exact ⟨BHist.Empty, ⟨unary_empty, unary_empty, cont_right_unit BHist.Empty⟩,
    NatBinom.left unary_empty⟩

theorem FactorialUp_constructive_export :
    (∀ {n : BHist}, UnaryHistory n -> ∃ f : BHist, UnaryHistory f ∧ NatFactorial n f) ∧
      (∀ {n f g : BHist}, NatFactorial n f -> NatFactorial n g -> hsame f g) ∧
      (∀ {n f : BHist}, NatFactorial n f -> hsame f BHist.Empty -> False) ∧
      (∀ {n k left right sum : BHist},
        NatChoose n k left -> NatChoose n (BHist.e1 k) right ->
          NatAdd left right sum -> NatChoose (BHist.e1 n) (BHist.e1 k) sum) ∧
      (∀ {n k c l : BHist}, NatChoose n k c -> NatChoose.Complementary k l n ->
        NatChoose n l c) := by
  constructor
  · intro n nUnary
    exact NatFactorial.total nUnary
  · constructor
    · intro n f g left right
      exact NatFactorial.functional left right
    · constructor
      · intro n f factorial empty
        exact NatFactorial.factorial_pos factorial empty
      · constructor
        · intro n k left right sum leftChoose rightChoose add
          exact NatChoose.pascal leftChoose rightChoose add
        · intro n k c l choose complementary
          exact NatChoose.choose_symm choose complementary

end BEDC.Derived.FactorialUp
