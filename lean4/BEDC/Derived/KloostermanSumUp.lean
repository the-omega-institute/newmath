import BEDC.Derived.RationalOrderArithUp
import BEDC.Derived.ZModResidueList

namespace BEDC.Derived.KloostermanSumUp

open BEDC.Algebra.FiniteFold
open BEDC.Algebra.Rel
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.FermatWilsonUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalOrderArithUp
open BEDC.Derived.RationalUp
open BEDC.Derived.ZModFieldUp
open BEDC.Derived.ZModResidueList
open BEDC.Derived.ZModUp

instance instDecidableZModNonzero {p : BHist} (x : ZMod p) :
    Decidable (zmodNonzero x) := by
  unfold zmodNonzero hsame
  infer_instance

structure RootOfUnityPacket (p : BHist) where
  carrier : Type
  eqv : carrier -> carrier -> Prop
  ring : RelCommRing carrier eqv
  zetaPow : ZMod p -> carrier
  zetaPow_respects : ∀ {x y : ZMod p}, zmodEq x y -> eqv (zetaPow x) (zetaPow y)

def zmodInvTotal {p : BHist} (prime : NatPrime p) (x : ZMod p) : ZMod p :=
  if hx : zmodNonzero x then
    zmodInv prime x hx
  else
    zmodZero p prime.left (NatPrime_empty_absurd prime)

theorem zmodInvTotal_of_nonzero {p : BHist} (prime : NatPrime p)
    {x : ZMod p} (hx : zmodNonzero x) :
    zmodEq (zmodInvTotal prime x) (zmodInv prime x hx) := by
  unfold zmodInvTotal
  rw [dif_pos hx]
  exact zmodEq_refl (zmodInv prime x hx)

theorem zmodInvTotal_nonzero {p : BHist} (prime : NatPrime p)
    {x : ZMod p} :
    zmodNonzero x -> zmodNonzero (zmodInvTotal prime x) := by
  intro hx
  unfold zmodInvTotal
  rw [dif_pos hx]
  exact zmodInv_nonzero prime x hx

theorem zmodInvTotal_mul_self {p : BHist} (prime : NatPrime p)
    {x : ZMod p} (hx : zmodNonzero x) :
    zmodEq
      (zmodMul p prime.left (NatPrime_empty_absurd prime) x
        (zmodInvTotal prime x))
      (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  exact zmodEq_trans
    (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
      (zmodEq_refl x) (zmodInvTotal_of_nonzero prime hx))
    (zmodInv_mul prime x hx)

theorem zmodInvTotal_left_mul_self {p : BHist} (prime : NatPrime p)
    {x : ZMod p} (hx : zmodNonzero x) :
    zmodEq
      (zmodMul p prime.left (NatPrime_empty_absurd prime)
        (zmodInvTotal prime x) x)
      (zmodOne p prime.left (NatPrime_empty_absurd prime)) := by
  exact zmodEq_trans
    (zmodMul_congr prime.left (NatPrime_empty_absurd prime)
      (zmodInvTotal_of_nonzero prime hx) (zmodEq_refl x))
    (zmodMul_inv prime x hx)

theorem zmodInvTotal_involutive {p : BHist} (prime : NatPrime p)
    {x : ZMod p} (hx : zmodNonzero x) :
    zmodEq (zmodInvTotal prime (zmodInvTotal prime x)) x := by
  let invX := zmodInvTotal prime x
  have invXNonzero : zmodNonzero invX :=
    zmodInvTotal_nonzero prime hx
  have leftUnit :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime) invX
          (zmodInvTotal prime invX))
        (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
    zmodInvTotal_mul_self prime invXNonzero
  have rightUnit :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime) invX x)
        (zmodOne p prime.left (NatPrime_empty_absurd prime)) :=
    zmodInvTotal_left_mul_self prime hx
  exact zmodMul_left_cancel_nonzero prime invXNonzero
    (zmodEq_trans leftUnit (zmodEq_symm rightUnit))

theorem zmodInvTotal_map_nodup {p : BHist} (prime : NatPrime p) :
    ListNoDup (List.map (zmodInvTotal prime) (nonzeroResidues prime)) := by
  exact listNoDup_map_of_left_inverse
    (zmodInvTotal prime) (zmodInvTotal prime)
    (nonzeroResidues prime) (nonzeroResidues_nodup prime)
    (fun x xMem =>
      zmod_ext
        (zmodInvTotal_involutive prime
          (nonzeroResidues_all_nonzero prime x xMem)))

theorem zmodInvTotal_mem_iff_nonzeroResidues {p : BHist} (prime : NatPrime p)
    (y : ZMod p) :
    y ∈ List.map (zmodInvTotal prime) (nonzeroResidues prime) ↔
      y ∈ nonzeroResidues prime := by
  constructor
  · intro mappedMem
    cases listMap_mem_extract (zmodInvTotal prime) mappedMem with
    | intro source sourceData =>
        cases sourceData with
        | intro sourceMem sourceEq =>
            rw [← sourceEq]
            exact nonzero_residues_complete prime (zmodInvTotal prime source)
              (zmodInvTotal_nonzero prime
                (nonzeroResidues_all_nonzero prime source sourceMem))
  · intro yMem
    have yNonzero : zmodNonzero y :=
      nonzeroResidues_all_nonzero prime y yMem
    let preimage := zmodInvTotal prime y
    have preimageMem : preimage ∈ nonzeroResidues prime :=
      nonzero_residues_complete prime preimage
        (zmodInvTotal_nonzero prime yNonzero)
    have imageEq : zmodInvTotal prime preimage = y :=
      zmod_ext (zmodInvTotal_involutive prime yNonzero)
    rw [← imageEq]
    exact listMap_mem_intro (zmodInvTotal prime) preimageMem

theorem zmodInvTotal_permutes_nonzeroResidues {p : BHist} (prime : NatPrime p) :
    ListPerm (List.map (zmodInvTotal prime) (nonzeroResidues prime))
      (nonzeroResidues prime) := by
  exact listPerm_of_noDup_mem_iff
    (List.map (zmodInvTotal prime) (nonzeroResidues prime))
    (nonzeroResidues prime)
    (zmodInvTotal_map_nodup prime)
    (nonzeroResidues_nodup prime)
    (fun y => zmodInvTotal_mem_iff_nonzeroResidues prime y)

def kloostermanPhase {p : BHist} (prime : NatPrime p)
    (a b x : ZMod p) : ZMod p :=
  zmodAdd p prime.left (NatPrime_empty_absurd prime)
    (zmodMul p prime.left (NatPrime_empty_absurd prime) a x)
    (zmodMul p prime.left (NatPrime_empty_absurd prime) b
      (zmodInvTotal prime x))

def KloostermanTerm {p : BHist} (root : RootOfUnityPacket p)
    (prime : NatPrime p) (a b x : ZMod p) : root.carrier :=
  root.zetaPow (kloostermanPhase prime a b x)

def KloostermanSum {p : BHist} (root : RootOfUnityPacket p)
    (prime : NatPrime p) (a b : ZMod p) : root.carrier :=
  listSum root.ring
    (List.map (KloostermanTerm root prime a b) (nonzeroResidues prime))

theorem kloostermanPhase_swap_at_invTotal {p : BHist} (prime : NatPrime p)
    (a b x : ZMod p) :
    zmodNonzero x ->
      zmodEq (kloostermanPhase prime a b x)
        (kloostermanPhase prime b a (zmodInvTotal prime x)) := by
  intro hx
  unfold kloostermanPhase
  have invInv :
      zmodEq (zmodInvTotal prime (zmodInvTotal prime x)) x :=
    zmodInvTotal_involutive prime hx
  have rightTerm :
      zmodEq
        (zmodMul p prime.left (NatPrime_empty_absurd prime) a x)
        (zmodMul p prime.left (NatPrime_empty_absurd prime) a
          (zmodInvTotal prime (zmodInvTotal prime x))) :=
    zmodMul_congr prime.left (NatPrime_empty_absurd prime)
      (zmodEq_refl a) (zmodEq_symm invInv)
  exact zmodEq_trans
    (zmodAdd_comm prime.left (NatPrime_empty_absurd prime)
      (zmodMul p prime.left (NatPrime_empty_absurd prime) a x)
      (zmodMul p prime.left (NatPrime_empty_absurd prime) b
        (zmodInvTotal prime x)))
    (zmodAdd_congr prime.left (NatPrime_empty_absurd prime)
      (zmodEq_refl
        (zmodMul p prime.left (NatPrime_empty_absurd prime) b
          (zmodInvTotal prime x)))
      rightTerm)

theorem kloostermanTerm_swap_at_invTotal {p : BHist}
    (root : RootOfUnityPacket p) (prime : NatPrime p)
    (a b x : ZMod p) :
    zmodNonzero x ->
      root.eqv (KloostermanTerm root prime a b x)
        (KloostermanTerm root prime b a (zmodInvTotal prime x)) := by
  intro hx
  exact root.zetaPow_respects
    (kloostermanPhase_swap_at_invTotal prime a b x hx)

theorem listSum_map_rel_of_mem {A : Type u} {B : Type v}
    {rel : B -> B -> Prop} (R : RelCommRing B rel)
    (f g : A -> B) :
    ∀ xs : List A,
      (∀ x : A, x ∈ xs -> rel (f x) (g x)) ->
        rel (listSum R (List.map f xs)) (listSum R (List.map g xs))
  | [], _pointwise =>
      R.refl R.zero
  | x :: xs, pointwise => by
      exact R.add_congr
        (pointwise x (List.Mem.head xs))
        (listSum_map_rel_of_mem R f g xs
          (fun y yMem => pointwise y (List.Mem.tail x yMem)))

theorem listMap_comp {A : Type u} {B : Type v} {C : Type w}
    (f : B -> C) (g : A -> B) :
    ∀ xs : List A, List.map f (List.map g xs) =
      List.map (fun x : A => f (g x)) xs
  | [] => rfl
  | _x :: xs => by
      change f (g _x) :: List.map f (List.map g xs) =
        f (g _x) :: List.map (fun x : A => f (g x)) xs
      rw [listMap_comp f g xs]

theorem kloostermanSum_swap_coefficients {p : BHist}
    (root : RootOfUnityPacket p) (prime : NatPrime p)
    (a b : ZMod p) :
    root.eqv (KloostermanSum root prime a b)
      (KloostermanSum root prime b a) := by
  unfold KloostermanSum
  let xs := nonzeroResidues prime
  have pointwise :
      root.eqv
        (listSum root.ring (List.map (KloostermanTerm root prime a b) xs))
        (listSum root.ring
          (List.map
            (fun x : ZMod p =>
              KloostermanTerm root prime b a (zmodInvTotal prime x))
            xs)) :=
    listSum_map_rel_of_mem root.ring
      (KloostermanTerm root prime a b)
      (fun x : ZMod p =>
        KloostermanTerm root prime b a (zmodInvTotal prime x))
      xs
      (fun x xMem =>
        kloostermanTerm_swap_at_invTotal root prime a b x
          (nonzeroResidues_all_nonzero prime x xMem))
  have reindexed :
      root.eqv
        (listSum root.ring
          (List.map
            (fun x : ZMod p =>
              KloostermanTerm root prime b a (zmodInvTotal prime x))
            xs))
        (listSum root.ring (List.map (KloostermanTerm root prime b a) xs)) := by
    have mapEq :
        List.map
            (fun x : ZMod p =>
              KloostermanTerm root prime b a (zmodInvTotal prime x))
            xs =
          List.map (KloostermanTerm root prime b a)
            (List.map (zmodInvTotal prime) xs) :=
      (listMap_comp (KloostermanTerm root prime b a)
        (zmodInvTotal prime) xs).symm
    rw [mapEq]
    exact sum_permInvariant root.ring
      (listPerm_map (KloostermanTerm root prime b a)
        (zmodInvTotal_permutes_nonzeroResidues prime))
  exact root.ring.trans pointwise reindexed

structure KloostermanWeilBoundWindow {p : BHist}
    (root : RootOfUnityPacket p) where
  magnitude : root.carrier -> RatNum
  sqrtPrimeUpper : RatNum

def KloostermanWeilBoundTarget {p : BHist}
    (root : RootOfUnityPacket p) (prime : NatPrime p)
    (a b : ZMod p) (window : KloostermanWeilBoundWindow root) : Prop :=
  ratLe
    (window.magnitude (KloostermanSum root prime a b))
    (ratMul ratTwo window.sqrtPrimeUpper)

def natPositiveBelowFrom (p current : Nat) : Nat -> List Nat
  | 0 => []
  | fuel + 1 =>
      if current < p then
        current :: natPositiveBelowFrom p (current + 1) fuel
      else
        []

def natPositiveBelow (p : Nat) : List Nat :=
  natPositiveBelowFrom p 1 p

def invModNatScan (p x candidate : Nat) : Nat -> Nat
  | 0 => 0
  | fuel + 1 =>
      if (x * candidate) % p = 1 % p then
        candidate % p
      else
        invModNatScan p x (candidate + 1) fuel

def invModNatFuel (p x fuel : Nat) : Nat :=
  invModNatScan p x 1 fuel

def kloostermanPhaseNat (p a b x fuel : Nat) : Nat :=
  (a * x + b * invModNatFuel p x fuel) % p

def kloostermanPhaseResiduesNat (p a b fuel : Nat) : List Nat :=
  List.map (fun x : Nat => kloostermanPhaseNat p a b x fuel)
    (natPositiveBelow p)

theorem natPositiveBelow_two :
    natPositiveBelow 2 = [1] := by
  decide

theorem natPositiveBelow_three :
    natPositiveBelow 3 = [1, 2] := by
  decide

theorem invModNatFuel_three_two :
    invModNatFuel 3 2 3 = 2 := by
  decide

theorem kloostermanPhaseResiduesNat_two_one_one :
    kloostermanPhaseResiduesNat 2 1 1 2 = [0] := by
  decide

theorem kloostermanPhaseResiduesNat_three_one_one :
    kloostermanPhaseResiduesNat 3 1 1 3 = [2, 1] := by
  decide

theorem kloostermanPhaseResiduesNat_five_two_three :
    kloostermanPhaseResiduesNat 5 2 3 5 = [0, 3, 2, 0] := by
  decide

theorem kloostermanPhaseResiduesNat_five_three_two :
    kloostermanPhaseResiduesNat 5 3 2 5 = [0, 2, 3, 0] := by
  decide

end BEDC.Derived.KloostermanSumUp
