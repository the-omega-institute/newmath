import BedcMathlibBridge.Constructive.ZMod
import BEDC.Derived.IntUp.Arithmetic

namespace BedcMathlibBridge.Export.ZMod

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.FKernel.ExternalBinary
open BEDC.Derived.NatUp
open BEDC.Derived.ZModUp

private theorem hsame_of_unary_length_eq {h k : BHist}
    (hUnary : UnaryHistory h) (kUnary : UnaryHistory k)
    (lengthEq : bwordLength h = bwordLength k) : hsame h k := by
  exact (NatUp_unary_standard_bridge.right.right.right.left hUnary kUnary).mpr lengthEq

private theorem strictPrefix_length_lt {h k : BHist}
    (hUnary : UnaryHistory h) (strict : NatUnaryStrictPrefix h k) :
    bwordLength h < bwordLength k := by
  rcases strict with ⟨tail, tailUnary, tailNonempty, tailCont⟩
  have lengthK :
      bwordLength k = bwordLength h + bwordLength tail :=
    NatUp_unary_standard_bridge.right.right.right.right hUnary tailUnary tailCont
  have tailPositive : 0 < bwordLength tail := by
    exact Nat.pos_of_ne_zero (fun tailZero => by
      have tailSameEmpty : hsame tail BHist.Empty :=
        hsame_of_unary_length_eq tailUnary unary_empty
          (tailZero.trans NatUp_unary_standard_bridge.left.symm)
      exact tailNonempty tailSameEmpty)
  rw [lengthK]
  exact Nat.lt_add_of_pos_right tailPositive

private theorem zmodVal_length_lt {n : BHist} (nUnary : UnaryHistory n) (x : ZMod n) :
    bwordLength x.val < bwordLength n := by
  exact strictPrefix_length_lt (zmodVal_unary nUnary x) x.isLt

private def bedcToFin {n : BHist} (nUnary : UnaryHistory n)
    (x : ZMod n) : Fin (bwordLength n) :=
  ⟨bwordLength x.val, zmodVal_length_lt nUnary x⟩

private def bedcOfFin (n : BHist) (nUnary : UnaryHistory n)
    (z : Fin (bwordLength n)) : ZMod n :=
  { val := BEDC.Derived.IntUp.natToUnary z.val
    isLt := by
      have valUnary := BEDC.Derived.IntUp.natToUnary_unary z.val
      have valLen :
          bwordLength (BEDC.Derived.IntUp.natToUnary z.val) = z.val :=
        BEDC.Derived.IntUp.natToUnary_length z.val
      have total := NatUnaryPrefix_total valUnary nUnary
      cases total with
      | inl forward =>
          rcases forward with ⟨tail, tailUnary, tailCont⟩
          cases NatUnaryPrefix_cont_tail_cases tailUnary tailCont with
          | inl same =>
              have lengthEq :=
                (NatUp_unary_standard_bridge.right.right.right.left valUnary nUnary).mp same
              rw [valLen] at lengthEq
              exact False.elim (Nat.ne_of_lt z.isLt lengthEq)
          | inr strict =>
              exact strict
      | inr backward =>
          rcases backward with ⟨tail, tailUnary, tailCont⟩
          have nLeVal : bwordLength n <= bwordLength (BEDC.Derived.IntUp.natToUnary z.val) := by
            rw [NatUp_unary_standard_bridge.right.right.right.right nUnary tailUnary tailCont]
            exact Nat.le_add_right _ _
          rw [valLen] at nLeVal
          exact False.elim (Nat.not_le_of_gt z.isLt nLeVal) }

private theorem bedcToFin_bedcOfFin {n : BHist} (nUnary : UnaryHistory n)
    (z : Fin (bwordLength n)) :
    bedcToFin nUnary (bedcOfFin n nUnary z) = z := by
  apply Fin.ext
  unfold bedcToFin bedcOfFin
  exact BEDC.Derived.IntUp.natToUnary_length z.val

private theorem bedcOfFin_bedcToFin_rel {n : BHist} (nUnary : UnaryHistory n)
    (x : ZMod n) :
    zmodEq (bedcOfFin n nUnary (bedcToFin nUnary x)) x := by
  apply (NatUp_unary_standard_bridge.right.right.right.left
    (zmodVal_unary nUnary (bedcOfFin n nUnary (bedcToFin nUnary x)))
    (zmodVal_unary nUnary x)).mpr
  unfold bedcOfFin bedcToFin
  exact BEDC.Derived.IntUp.natToUnary_length (bwordLength x.val)

private theorem zmodEq_iff_toFin_eq {n : BHist} (nUnary : UnaryHistory n) {x y : ZMod n} :
    zmodEq x y ↔ bedcToFin nUnary x = bedcToFin nUnary y := by
  constructor
  · intro rel
    apply Fin.ext
    unfold bedcToFin
    exact (NatUp_unary_standard_bridge.right.right.right.left
      (zmodVal_unary nUnary x) (zmodVal_unary nUnary y)).mp rel
  · intro h
    exact (NatUp_unary_standard_bridge.right.right.right.left
      (zmodVal_unary nUnary x) (zmodVal_unary nUnary y)).mpr
        (congrArg Fin.val h)

private def finZero {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : Fin (bwordLength n) :=
  bedcToFin nUnary (zmodZero n nUnary nNonempty)

private def finOne {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False) : Fin (bwordLength n) :=
  bedcToFin nUnary (zmodOne n nUnary nNonempty)

private def finAdd {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (x y : Fin (bwordLength n)) : Fin (bwordLength n) :=
  bedcToFin nUnary
    (zmodAdd n nUnary nNonempty (bedcOfFin n nUnary x) (bedcOfFin n nUnary y))

private def finNeg {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (x : Fin (bwordLength n)) : Fin (bwordLength n) :=
  bedcToFin nUnary (zmodNeg n nUnary nNonempty (bedcOfFin n nUnary x))

private def finMul {n : BHist} (nUnary : UnaryHistory n)
    (nNonempty : hsame n BHist.Empty -> False)
    (x y : Fin (bwordLength n)) : Fin (bwordLength n) :=
  bedcToFin nUnary
    (zmodMul n nUnary nNonempty (bedcOfFin n nUnary x) (bedcOfFin n nUnary y))

structure ZModExportWitness where
  toFin :
    ∀ {n : BHist}, UnaryHistory n -> ZMod n -> Fin (bwordLength n)
  ofFin :
    ∀ {n : BHist}, UnaryHistory n -> Fin (bwordLength n) -> ZMod n
  toFin_ofFin :
    ∀ {n : BHist} (nUnary : UnaryHistory n) (z : Fin (bwordLength n)),
      toFin nUnary (ofFin nUnary z) = z
  ofFin_toFin_rel :
    ∀ {n : BHist} (nUnary : UnaryHistory n) (x : ZMod n),
      zmodEq (ofFin nUnary (toFin nUnary x)) x
  zmodEq_apply :
    ∀ {n : BHist} (nUnary : UnaryHistory n) (x y : ZMod n),
      zmodEq x y ↔ toFin nUnary x = toFin nUnary y
  zero :
    ∀ {n : BHist}, (nUnary : UnaryHistory n) ->
      (hsame n BHist.Empty -> False) -> Fin (bwordLength n)
  one :
    ∀ {n : BHist}, (nUnary : UnaryHistory n) ->
      (hsame n BHist.Empty -> False) -> Fin (bwordLength n)
  add :
    ∀ {n : BHist}, (nUnary : UnaryHistory n) ->
      (hsame n BHist.Empty -> False) ->
      Fin (bwordLength n) -> Fin (bwordLength n) -> Fin (bwordLength n)
  neg :
    ∀ {n : BHist}, (nUnary : UnaryHistory n) ->
      (hsame n BHist.Empty -> False) ->
      Fin (bwordLength n) -> Fin (bwordLength n)
  mul :
    ∀ {n : BHist}, (nUnary : UnaryHistory n) ->
      (hsame n BHist.Empty -> False) ->
      Fin (bwordLength n) -> Fin (bwordLength n) -> Fin (bwordLength n)
  zero_apply :
    ∀ {n : BHist} (nUnary : UnaryHistory n)
      (nNonempty : hsame n BHist.Empty -> False),
      toFin nUnary (zmodZero n nUnary nNonempty) = zero nUnary nNonempty
  one_apply :
    ∀ {n : BHist} (nUnary : UnaryHistory n)
      (nNonempty : hsame n BHist.Empty -> False),
      toFin nUnary (zmodOne n nUnary nNonempty) = one nUnary nNonempty
  add_apply :
    ∀ {n : BHist} (nUnary : UnaryHistory n)
      (nNonempty : hsame n BHist.Empty -> False)
      (x y : Fin (bwordLength n)),
      toFin nUnary (zmodAdd n nUnary nNonempty (ofFin nUnary x) (ofFin nUnary y)) =
        add nUnary nNonempty x y
  neg_apply :
    ∀ {n : BHist} (nUnary : UnaryHistory n)
      (nNonempty : hsame n BHist.Empty -> False)
      (x : Fin (bwordLength n)),
      toFin nUnary (zmodNeg n nUnary nNonempty (ofFin nUnary x)) =
        neg nUnary nNonempty x
  mul_apply :
    ∀ {n : BHist} (nUnary : UnaryHistory n)
      (nNonempty : hsame n BHist.Empty -> False)
      (x y : Fin (bwordLength n)),
      toFin nUnary (zmodMul n nUnary nNonempty (ofFin nUnary x) (ofFin nUnary y)) =
        mul nUnary nNonempty x y
  mathlib_anchor :
    ∀ {n : BHist}, _root_.ZMod (bwordLength n) -> _root_.ZMod (bwordLength n)

def zmodExport : ZModExportWitness where
  toFin := bedcToFin
  ofFin := fun {n} nUnary z => bedcOfFin n nUnary z
  toFin_ofFin := bedcToFin_bedcOfFin
  ofFin_toFin_rel := bedcOfFin_bedcToFin_rel
  zmodEq_apply := fun nUnary x y => zmodEq_iff_toFin_eq nUnary
  zero := finZero
  one := finOne
  add := finAdd
  neg := finNeg
  mul := finMul
  zero_apply := by
    intro _ _ _
    rfl
  one_apply := by
    intro _ _ _
    rfl
  add_apply := by
    intro _ _ _ _ _
    rfl
  neg_apply := by
    intro _ _ _ _
    rfl
  mul_apply := by
    intro _ _ _ _ _
    rfl
  mathlib_anchor := fun z => z

def zmod_mathlib_correspondence_type :
    ∀ {n : BHist} (_ : UnaryHistory n)
      (_nNonempty : hsame n BHist.Empty -> False),
      (ZMod n -> Fin (bwordLength n)) ×
        (_root_.ZMod (bwordLength n) -> _root_.ZMod (bwordLength n)) :=
  fun nUnary _nNonempty =>
    (zmodExport.toFin nUnary, fun z => z)

end BedcMathlibBridge.Export.ZMod
