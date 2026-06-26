import BEDC.Algebra.FiniteFold
import BEDC.Derived.FactorialUp
import BEDC.Derived.FermatWilsonUp
import BEDC.Derived.GcdUp
import BEDC.Derived.PrimeUp.UnitResult
import BEDC.Derived.ZModFieldUp

namespace BEDC.Derived.ZModResidueList

open BEDC.Algebra.FiniteFold
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.FactorialUp
open BEDC.Derived.GcdUp
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.PadicUp
open BEDC.Derived.ZModUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.FermatWilsonUp

theorem zmod_ext {n : BHist} {x y : ZMod n} :
    zmodEq x y -> x = y := by
  intro same
  cases x with
  | mk xv xLt =>
      cases y with
      | mk yv yLt =>
          cases same
          rfl

inductive ListNoDup {A : Type u} : List A -> Prop where
  | nil : ListNoDup []
  | cons {x : A} {xs : List A} :
      (x ∈ xs -> False) -> ListNoDup xs -> ListNoDup (x :: xs)

theorem listNoDup_tail {A : Type u} {x : A} {xs : List A} :
    ListNoDup (x :: xs) -> ListNoDup xs := by
  intro nodup
  cases nodup with
  | cons _ tail =>
      exact tail

theorem listNoDup_head_not_mem {A : Type u} {x : A} {xs : List A} :
    ListNoDup (x :: xs) -> x ∈ xs -> False := by
  intro nodup
  cases nodup with
  | cons head _ =>
      exact head

theorem listPerm_mem {A : Type u} {xs ys : List A} :
    ListPerm xs ys -> ∀ a : A, a ∈ xs -> a ∈ ys := by
  intro perm
  induction perm with
  | nil =>
      intro a mem
      cases mem
  | cons x p ih =>
      intro a mem
      cases mem with
      | head =>
          exact List.Mem.head _
      | tail _ memTail =>
          exact List.Mem.tail x (ih a memTail)
  | swap x y xs =>
      intro a mem
      cases mem with
      | head =>
          exact List.Mem.tail y (List.Mem.head xs)
      | tail _ tailMem =>
          cases tailMem with
          | head =>
              exact List.Mem.head _
          | tail _ restMem =>
              exact List.Mem.tail y (List.Mem.tail x restMem)
  | trans p q ihp ihq =>
      intro a mem
      exact ihq a (ihp a mem)

theorem listPerm_noDup {A : Type u} {xs ys : List A} :
    ListPerm xs ys -> ListNoDup xs -> ListNoDup ys := by
  intro perm
  induction perm with
  | nil =>
      intro _nodup
      exact ListNoDup.nil
  | cons x p ih =>
      intro nodup
      exact ListNoDup.cons
        (fun xMemYs =>
          listNoDup_head_not_mem nodup
            (listPerm_mem (listPerm_symm p) x xMemYs))
        (ih (listNoDup_tail nodup))
  | swap x y xs =>
      intro nodup
      have xNotInYxs : x ∈ y :: xs -> False :=
        listNoDup_head_not_mem nodup
      have yxsNodup : ListNoDup (y :: xs) :=
        listNoDup_tail nodup
      have yNotInXs : y ∈ xs -> False :=
        listNoDup_head_not_mem yxsNodup
      have xsNodup : ListNoDup xs :=
        listNoDup_tail yxsNodup
      exact ListNoDup.cons
        (fun yMemXxs =>
          match yMemXxs with
          | List.Mem.head _ =>
              xNotInYxs (List.Mem.head xs)
          | List.Mem.tail _ yMemXs =>
              yNotInXs yMemXs)
        (ListNoDup.cons
          (fun xMemXs => xNotInYxs (List.Mem.tail y xMemXs))
          xsNodup)
  | trans p q ihp ihq =>
      intro nodup
      exact ihq (ihp nodup)

theorem listPerm_middle {A : Type u} (x : A) :
    ∀ left right : List A, ListPerm (left ++ x :: right) (x :: left ++ right)
  | [], right =>
      listPerm_refl (x :: right)
  | y :: ys, right => by
      change ListPerm (y :: (ys ++ x :: right)) (x :: y :: (ys ++ right))
      exact ListPerm.trans
        (ListPerm.cons y (listPerm_middle x ys right))
        (ListPerm.swap y x (ys ++ right))

theorem list_split_of_mem {A : Type u} {x : A} :
    ∀ {ys : List A}, x ∈ ys -> ∃ left right : List A, ys = left ++ x :: right
  | [], mem => by
      cases mem
  | y :: ys, mem => by
      cases mem with
      | head =>
          exact ⟨[], ys, rfl⟩
      | tail _ memTail =>
          cases list_split_of_mem memTail with
          | intro left data =>
              cases data with
              | intro right ysEq =>
                  exact ⟨y :: left, right, by rw [ysEq]; rfl⟩

theorem listPerm_of_noDup_mem_iff {A : Type u} :
    ∀ xs ys : List A, ListNoDup xs -> ListNoDup ys ->
      (∀ a : A, a ∈ xs ↔ a ∈ ys) -> ListPerm xs ys
  | [], ys, _xsNodup, _ysNodup, memIff => by
      cases ys with
      | nil =>
          exact ListPerm.nil
      | cons y ysTail =>
          have yInEmpty : y ∈ ([] : List A) :=
            (memIff y).mpr (List.Mem.head ysTail)
          cases yInEmpty
  | x :: xsTail, ys, xsNodup, ysNodup, memIff => by
      have xMemYs : x ∈ ys :=
        (memIff x).mp (List.Mem.head xsTail)
      cases list_split_of_mem xMemYs with
      | intro left data =>
          cases data with
          | intro right ysEq =>
              have permYsToX : ListPerm ys (x :: left ++ right) := by
                rw [ysEq]
                exact listPerm_middle x left right
              have nodupXRest : ListNoDup (x :: left ++ right) :=
                listPerm_noDup permYsToX ysNodup
              have restNodup : ListNoDup (left ++ right) :=
                listNoDup_tail nodupXRest
              have xNotXs : ¬x ∈ xsTail :=
                listNoDup_head_not_mem xsNodup
              have xNotRest : ¬x ∈ left ++ right :=
                listNoDup_head_not_mem nodupXRest
              have tailNodup : ListNoDup xsTail :=
                listNoDup_tail xsNodup
              have tailMemIff : ∀ a : A, a ∈ xsTail ↔ a ∈ left ++ right := by
                intro a
                constructor
                · intro aInTail
                  have aInYs : a ∈ ys :=
                    (memIff a).mp (List.Mem.tail x aInTail)
                  have aInXRest : a ∈ x :: left ++ right :=
                    listPerm_mem permYsToX a aInYs
                  cases aInXRest with
                  | head =>
                      exact False.elim (xNotXs aInTail)
                  | tail _ aInRest =>
                      exact aInRest
                · intro aInRest
                  have aInXRest : a ∈ x :: left ++ right :=
                    List.Mem.tail x aInRest
                  have aInYs : a ∈ ys :=
                    listPerm_mem (listPerm_symm permYsToX) a aInXRest
                  have aInXs : a ∈ x :: xsTail :=
                    (memIff a).mpr aInYs
                  cases aInXs with
                  | head =>
                      exact False.elim (xNotRest aInRest)
                  | tail _ aInTail =>
                      exact aInTail
              have tailPerm : ListPerm xsTail (left ++ right) :=
                listPerm_of_noDup_mem_iff xsTail (left ++ right)
                  tailNodup restNodup tailMemIff
              exact ListPerm.trans (ListPerm.cons x tailPerm)
                (listPerm_symm permYsToX)

theorem listMap_mem_extract {A : Type u} {B : Type v} (f : A -> B) :
    ∀ {xs : List A} {y : B}, y ∈ List.map f xs ->
      ∃ x : A, x ∈ xs ∧ f x = y
  | [], _y, mem => by
      cases mem
  | x :: xs, _y, mem => by
      cases mem with
      | head =>
          exact ⟨x, List.Mem.head xs, rfl⟩
      | tail _ memTail =>
          cases listMap_mem_extract f memTail with
          | intro z zData =>
              exact ⟨z, List.Mem.tail x zData.left, zData.right⟩

theorem listMap_mem_intro {A : Type u} {B : Type v} (f : A -> B)
    {xs : List A} {x : A} :
    x ∈ xs -> f x ∈ List.map f xs := by
  intro mem
  induction xs with
  | nil =>
      cases mem
  | cons y ys ih =>
      cases mem with
      | head =>
          exact List.Mem.head (List.map f ys)
      | tail _ memTail =>
          exact List.Mem.tail (f y) (ih memTail)

theorem listNoDup_map_of_left_inverse {A : Type u} {B : Type v}
    (f : A -> B) (g : B -> A) :
    ∀ xs : List A, ListNoDup xs ->
      (∀ x : A, x ∈ xs -> g (f x) = x) -> ListNoDup (List.map f xs)
  | [], _nodup, _leftInv =>
      ListNoDup.nil
  | x :: xs, nodup, leftInv => by
      exact ListNoDup.cons
        (by
          intro imageMemTail
          cases listMap_mem_extract f imageMemTail with
          | intro z zData =>
              have zMemXs : z ∈ xs := zData.left
              have zImageEq : f z = f x := zData.right
              have zEqX : z = x := by
                have zReduce : g (f z) = z :=
                  leftInv z (List.Mem.tail x zMemXs)
                have xReduce : g (f x) = x :=
                  leftInv x (List.Mem.head xs)
                rw [← zReduce, zImageEq, xReduce]
              exact listNoDup_head_not_mem nodup (zEqX ▸ zMemXs))
        (listNoDup_map_of_left_inverse f g xs
          (listNoDup_tail nodup)
          (fun z zMem => leftInv z (List.Mem.tail x zMem)))

def positiveUpTo : BHist -> List BHist
  | BHist.Empty => []
  | BHist.e0 _ => []
  | BHist.e1 tail => BHist.e1 tail :: positiveUpTo tail

def positiveBelow : BHist -> List BHist
  | BHist.Empty => []
  | BHist.e0 _ => []
  | BHist.e1 tail => positiveUpTo tail

theorem positiveUpTo_member_unary {n r : BHist} :
    UnaryHistory n -> r ∈ positiveUpTo n -> UnaryHistory r := by
  intro nUnary mem
  induction n with
  | Empty =>
      cases mem
  | e0 _ =>
      cases nUnary
  | e1 tail ih =>
      cases mem with
      | head =>
          exact unary_e1_closed nUnary
      | tail _ memTail =>
          exact ih nUnary memTail

theorem positiveUpTo_member_positive {n r : BHist} :
    UnaryHistory n -> r ∈ positiveUpTo n ->
      NatUnaryStrictPrefix BHist.Empty r := by
  intro nUnary mem
  induction n with
  | Empty =>
      cases mem
  | e0 _ =>
      cases nUnary
  | e1 tail ih =>
      cases mem with
      | head =>
          exact ⟨BHist.e1 tail, unary_e1_closed nUnary,
            (fun empty => by cases empty), cont_left_unit _⟩
      | tail _ memTail =>
          exact ih nUnary memTail

theorem positiveUpTo_member_lt_succ {n r : BHist} :
    UnaryHistory n -> r ∈ positiveUpTo n -> NatUnaryStrictPrefix r (BHist.e1 n) := by
  intro nUnary mem
  induction n with
  | Empty =>
      cases mem
  | e0 _ =>
      cases nUnary
  | e1 tail ih =>
      cases mem with
      | head =>
          exact NatUnaryStrictPrefix_one_step (unary_e1_closed nUnary)
      | tail _ memTail =>
          exact NatUnaryStrictPrefix_trans (ih nUnary memTail)
            (NatUnaryStrictPrefix_one_step (unary_e1_closed nUnary))

theorem positiveUpTo_complete {n r : BHist} :
    UnaryHistory n -> UnaryHistory r -> NatUnaryStrictPrefix BHist.Empty r ->
      (hsame r n ∨ NatUnaryStrictPrefix r n) -> r ∈ positiveUpTo n := by
  intro nUnary rUnary rPositive bound
  induction n generalizing r with
  | Empty =>
      cases bound with
      | inl same =>
          cases same
          exact False.elim (NatUnaryStrictPrefix_empty_right_absurd rPositive)
      | inr strict =>
          exact False.elim (NatUnaryStrictPrefix_empty_right_absurd strict)
  | e0 _ =>
      cases nUnary
  | e1 tail ih =>
      cases bound with
      | inl same =>
          cases same
          exact List.Mem.head (positiveUpTo tail)
      | inr strict =>
          have localBound := NatUnaryStrictPrefix_successor_boundary_local rUnary strict
          exact List.Mem.tail (BHist.e1 tail)
            (ih nUnary rUnary rPositive localBound)

theorem positiveUpTo_nodup {n : BHist} :
    UnaryHistory n -> ListNoDup (positiveUpTo n) := by
  intro nUnary
  induction n with
  | Empty =>
      exact ListNoDup.nil
  | e0 _ =>
      cases nUnary
  | e1 tail ih =>
      exact ListNoDup.cons
        (fun headInTail =>
          have strictSelf :
              NatUnaryStrictPrefix (BHist.e1 tail) (BHist.e1 tail) :=
            positiveUpTo_member_lt_succ nUnary headInTail
          NatUnaryStrictPrefix_asymm strictSelf strictSelf)
        (ih nUnary)

theorem positiveBelow_member_lt {p r : BHist} :
    UnaryHistory p -> r ∈ positiveBelow p -> NatUnaryStrictPrefix r p := by
  intro pUnary mem
  cases p with
  | Empty =>
      cases mem
  | e0 _ =>
      cases pUnary
  | e1 tail =>
      change r ∈ positiveUpTo tail at mem
      exact positiveUpTo_member_lt_succ (unary_e1_inversion pUnary) mem

theorem positiveBelow_member_positive {p r : BHist} :
    UnaryHistory p -> r ∈ positiveBelow p ->
      NatUnaryStrictPrefix BHist.Empty r := by
  intro pUnary mem
  cases p with
  | Empty =>
      cases mem
  | e0 _ =>
      cases pUnary
  | e1 tail =>
      change r ∈ positiveUpTo tail at mem
      exact positiveUpTo_member_positive (unary_e1_inversion pUnary) mem

theorem positiveBelow_complete {p r : BHist} :
    UnaryHistory p -> UnaryHistory r -> NatUnaryStrictPrefix BHist.Empty r ->
      NatUnaryStrictPrefix r p -> r ∈ positiveBelow p := by
  intro pUnary rUnary rPositive rLtP
  cases p with
  | Empty =>
      exact False.elim (NatUnaryStrictPrefix_empty_right_absurd rLtP)
  | e0 _ =>
      cases pUnary
  | e1 tail =>
      change r ∈ positiveUpTo tail
      have bound := NatUnaryStrictPrefix_successor_boundary_local rUnary rLtP
      exact positiveUpTo_complete (unary_e1_inversion pUnary) rUnary rPositive bound

def residueListFrom {p : BHist} (xs : List BHist)
    (bounded : ∀ r : BHist, r ∈ xs -> NatUnaryStrictPrefix r p) : List (ZMod p) :=
  match xs with
  | [] => []
  | r :: rs =>
      { val := r
        isLt := bounded r (List.Mem.head rs) } ::
        residueListFrom rs
          (fun x mem => bounded x (List.Mem.tail r mem))

def residueOfPositive {p : BHist} (prime : NatPrime p) (r : BHist)
    (mem : r ∈ positiveBelow p) : ZMod p :=
  { val := r
    isLt := positiveBelow_member_lt prime.left mem }

def nonzeroResidues {p : BHist} (prime : NatPrime p) : List (ZMod p) :=
  residueListFrom (positiveBelow p)
    (fun _x mem => positiveBelow_member_lt prime.left mem)

theorem positive_member_not_empty {p r : BHist} :
    UnaryHistory p -> r ∈ positiveBelow p ->
      hsame r BHist.Empty -> False := by
  intro pUnary mem rEmpty
  have positive := positiveBelow_member_positive pUnary mem
  cases rEmpty
  exact NatUnaryStrictPrefix_empty_right_absurd positive

theorem residueListFrom_all_nonzero {p : BHist} (_prime : NatPrime p)
    (xs : List BHist)
    (bounded : ∀ r : BHist, r ∈ xs -> NatUnaryStrictPrefix r p)
    (positive : ∀ r : BHist, r ∈ xs -> NatUnaryStrictPrefix BHist.Empty r) :
    ∀ x : ZMod p, x ∈ residueListFrom xs bounded -> zmodNonzero x := by
  intro x mem
  induction xs with
  | nil =>
      cases mem
  | cons r rs ih =>
      unfold residueListFrom at mem
      cases mem with
      | head =>
          change hsame r BHist.Empty -> False
          intro rEmpty
          cases rEmpty
          exact NatUnaryStrictPrefix_empty_right_absurd
            (positive BHist.Empty (List.Mem.head rs))
      | tail _ memTail =>
          exact ih
            (fun y yMem => bounded y (List.Mem.tail r yMem))
            (fun y yMem => positive y (List.Mem.tail r yMem))
            memTail

theorem residueListFrom_complete {p : BHist}
    (xs : List BHist)
    (bounded : ∀ r : BHist, r ∈ xs -> NatUnaryStrictPrefix r p)
    (x : ZMod p) :
    x.val ∈ xs -> x ∈ residueListFrom xs bounded := by
  intro mem
  induction xs with
  | nil =>
      cases mem
  | cons r rs ih =>
      unfold residueListFrom
      cases mem with
      | head =>
          exact List.Mem.head _
      | tail _ memTail =>
          exact List.Mem.tail _
            (ih (fun y yMem => bounded y (List.Mem.tail r yMem)) memTail)

theorem residueListFrom_member_raw {p : BHist}
    (xs : List BHist)
    (bounded : ∀ r : BHist, r ∈ xs -> NatUnaryStrictPrefix r p)
    (x : ZMod p) :
    x ∈ residueListFrom xs bounded -> x.val ∈ xs := by
  intro mem
  induction xs with
  | nil =>
      cases mem
  | cons r rs ih =>
      unfold residueListFrom at mem
      cases mem with
      | head =>
          exact List.Mem.head rs
      | tail _ memTail =>
          exact List.Mem.tail r
            (ih
              (fun y yMem => bounded y (List.Mem.tail r yMem))
              memTail)

theorem nonzeroResidues_all_nonzero {p : BHist} (prime : NatPrime p) :
    ∀ x : ZMod p, x ∈ nonzeroResidues prime -> zmodNonzero x := by
  intro x mem
  exact residueListFrom_all_nonzero prime (positiveBelow p)
    (fun r rawMem => positiveBelow_member_lt prime.left rawMem)
    (fun r rawMem => positiveBelow_member_positive prime.left rawMem)
    x mem

theorem nonzero_residues_complete {p : BHist} (prime : NatPrime p)
    (x : ZMod p) :
    zmodNonzero x -> x ∈ nonzeroResidues prime := by
  intro xNonzero
  have xUnary : UnaryHistory x.val := zmodVal_unary prime.left x
  have xPositive : NatUnaryStrictPrefix BHist.Empty x.val :=
    NatUnary_nonempty_positive_for_divides_closure xUnary xNonzero
  have memRaw : x.val ∈ positiveBelow p :=
    positiveBelow_complete prime.left xUnary xPositive x.isLt
  unfold nonzeroResidues
  exact residueListFrom_complete (positiveBelow p)
    (fun r rawMem => positiveBelow_member_lt prime.left rawMem)
    x memRaw

theorem positiveBelow_nodup {p : BHist} :
    UnaryHistory p -> ListNoDup (positiveBelow p) := by
  intro pUnary
  cases p with
  | Empty =>
      exact ListNoDup.nil
  | e0 _ =>
      cases pUnary
  | e1 tail =>
      change ListNoDup (positiveUpTo tail)
      exact positiveUpTo_nodup (unary_e1_inversion pUnary)

theorem residueListFrom_nodup {p : BHist}
    (xs : List BHist)
    (bounded : ∀ r : BHist, r ∈ xs -> NatUnaryStrictPrefix r p) :
    ListNoDup xs -> ListNoDup (residueListFrom xs bounded) := by
  intro xsNodup
  induction xs with
  | nil =>
      exact ListNoDup.nil
  | cons r rs ih =>
      unfold residueListFrom
      have rNotInRs : ¬r ∈ rs :=
        listNoDup_head_not_mem xsNodup
      have rsNodup : ListNoDup rs :=
        listNoDup_tail xsNodup
      exact ListNoDup.cons
        (fun rMemTail =>
          rNotInRs
            (residueListFrom_member_raw rs
              (fun x mem => bounded x (List.Mem.tail r mem))
              { val := r
                isLt := bounded r (List.Mem.head rs) }
              rMemTail))
        (ih
          (fun x mem => bounded x (List.Mem.tail r mem))
          rsNodup)

theorem nonzeroResidues_nodup {p : BHist} (prime : NatPrime p) :
    ListNoDup (nonzeroResidues prime) := by
  unfold nonzeroResidues
  exact residueListFrom_nodup (positiveBelow p)
    (fun r rawMem => positiveBelow_member_lt prime.left rawMem)
    (positiveBelow_nodup prime.left)

theorem zmodInv_nonzero {p : BHist} (prime : NatPrime p)
    (x : ZMod p) (hx : zmodNonzero x) :
    zmodNonzero (zmodInv prime x hx) := by
  intro invEmpty
  have productEmpty :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime)
          x (zmodInv prime x hx))
        (zmodZero p prime.left (NatPrime_empty_absurd prime)) := by
    exact zmodEq_trans
      (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
        (zmodEq_refl x)
        (by
          change hsame (zmodInv prime x hx).val BHist.Empty
          exact invEmpty))
      (BEDC.Derived.LegendreUp.zmodMul_zero_right prime x)
  have oneEmpty :
      zmodEq
        (zmodOne p prime.left (NatPrime_empty_absurd prime))
        (zmodZero p prime.left (NatPrime_empty_absurd prime)) :=
    zmodEq_trans (zmodEq_symm (zmodInv_mul prime x hx)) productEmpty
  exact zmodOne_nonzero prime oneEmpty

theorem zmodUnitMul_mem_nonzeroResidues {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) (x : ZMod p) :
    x ∈ nonzeroResidues prime ->
      zmodUnitMul prime a aNonzero x ∈ nonzeroResidues prime := by
  intro xMem
  exact nonzero_residues_complete prime
    (zmodUnitMul prime a aNonzero x)
    (zmodUnitMul_nonzero prime a aNonzero
      (nonzeroResidues_all_nonzero prime x xMem))

theorem zmodUnitMul_mem_iff_nonzeroResidues {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) (y : ZMod p) :
    y ∈ List.map (fun x : ZMod p => zmodUnitMul prime a aNonzero x)
        (nonzeroResidues prime) ↔ y ∈ nonzeroResidues prime := by
  constructor
  · intro mappedMem
    cases listMap_mem_extract
        (fun x : ZMod p => zmodUnitMul prime a aNonzero x)
        mappedMem with
    | intro source sourceData =>
        cases sourceData with
        | intro sourceMem sourceEq =>
            rw [← sourceEq]
            exact zmodUnitMul_mem_nonzeroResidues prime a aNonzero source sourceMem
  · intro yMem
    let invA := zmodInv prime a aNonzero
    have invANonzero : zmodNonzero invA :=
      zmodInv_nonzero prime a aNonzero
    let preimage := zmodUnitMul prime invA invANonzero y
    have preimageMem : preimage ∈ nonzeroResidues prime :=
      zmodUnitMul_mem_nonzeroResidues prime invA invANonzero y yMem
    have imageEq :
        zmodUnitMul prime a aNonzero preimage = y :=
      zmod_ext (zmodUnitMul_unitDiv prime a aNonzero y)
    rw [← imageEq]
    exact listMap_mem_intro
      (fun x : ZMod p => zmodUnitMul prime a aNonzero x)
      preimageMem

theorem zmodUnitMul_map_nodup {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) :
    ListNoDup
      (List.map (fun x : ZMod p => zmodUnitMul prime a aNonzero x)
        (nonzeroResidues prime)) := by
  let f := fun x : ZMod p => zmodUnitMul prime a aNonzero x
  let g := fun y : ZMod p => zmodUnitDiv prime a aNonzero y
  change ListNoDup (List.map f (nonzeroResidues prime))
  exact listNoDup_map_of_left_inverse f g
    (nonzeroResidues prime) (nonzeroResidues_nodup prime)
    (fun x _xMem => zmod_ext (zmodUnitDiv_unitMul prime a aNonzero x))

theorem mulByUnit_permutes {p : BHist} (prime : NatPrime p)
    (a : ZMod p) (aNonzero : zmodNonzero a) :
    ListPerm
      (List.map (fun x : ZMod p => zmodUnitMul prime a aNonzero x)
        (nonzeroResidues prime))
      (nonzeroResidues prime) := by
  exact listPerm_of_noDup_mem_iff
    (List.map (fun x : ZMod p => zmodUnitMul prime a aNonzero x)
      (nonzeroResidues prime))
    (nonzeroResidues prime)
    (zmodUnitMul_map_nodup prime a aNonzero)
    (nonzeroResidues_nodup prime)
    (fun y => zmodUnitMul_mem_iff_nonzeroResidues prime a aNonzero y)

theorem zmodFromNat_gcd_one_nonzero {p a : BHist} (prime : NatPrime p)
    (aUnary : UnaryHistory a) :
    NatGcd a p (BHist.e1 BHist.Empty) ->
      zmodNonzero
        (zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary) := by
  intro gcd residueEmpty
  have pDividesA : NatDivides p a :=
    (dvd_iff_mod_zero prime.left (NatPrime_empty_absurd prime) aUnary).mpr
      residueEmpty
  have pDividesP : NatDivides p p :=
    (NatDivides_reflexive_pair prime.left).right
  have pDividesOne : NatDivides p (BHist.e1 BHist.Empty) :=
    NatGcd_greatest gcd pDividesA pDividesP
  have pUnit : hsame p (BHist.e1 BHist.Empty) :=
    NatDivides_unit_right_iff.mp pDividesOne
  cases pUnit
  exact NatPrime_unit_absurd prime

theorem mulByCoprime_permutes {p a : BHist} (prime : NatPrime p)
    (aUnary : UnaryHistory a)
    (gcd : NatGcd a p (BHist.e1 BHist.Empty)) :
    ListPerm
      (List.map
        (fun x : ZMod p =>
          zmodUnitMul prime
            (zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary)
            (zmodFromNat_gcd_one_nonzero prime aUnary gcd) x)
        (nonzeroResidues prime))
      (nonzeroResidues prime) := by
  exact mulByUnit_permutes prime
    (zmodFromNat p prime.left (NatPrime_empty_absurd prime) a aUnary)
    (zmodFromNat_gcd_one_nonzero prime aUnary gcd)

theorem nonzeroResidues_nonempty_product_unit {p : BHist} (prime : NatPrime p) :
    zmodNonzero
      (listProd (zmodRelCommRing prime) (nonzeroResidues prime)) := by
  exact zmodListProd_nonzero prime (nonzeroResidues prime)
    (nonzeroResidues_all_nonzero prime)

end BEDC.Derived.ZModResidueList
