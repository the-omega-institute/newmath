import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionReflectiveSubcategoryUp
namespace TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionReflectiveSubcategoryUp : Type where
  | mk (S M J U Q E Z T H C P N : BHist) : CauchyCompletionReflectiveSubcategoryUp
  deriving DecidableEq

def cauchyCompletionReflectiveSubcategoryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionReflectiveSubcategoryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionReflectiveSubcategoryEncodeBHist h

def cauchyCompletionReflectiveSubcategoryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionReflectiveSubcategoryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionReflectiveSubcategoryDecodeBHist tail)

private theorem CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionReflectiveSubcategoryFields :
    CauchyCompletionReflectiveSubcategoryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionReflectiveSubcategoryUp.mk S M J U Q E Z T H C P N =>
      [S, M, J, U, Q, E, Z, T, H, C, P, N]

def cauchyCompletionReflectiveSubcategoryToEventFlow :
    CauchyCompletionReflectiveSubcategoryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (cauchyCompletionReflectiveSubcategoryFields x).map
        cauchyCompletionReflectiveSubcategoryEncodeBHist

private def cauchyCompletionReflectiveSubcategoryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyCompletionReflectiveSubcategoryEventAtDefault index rest

def cauchyCompletionReflectiveSubcategoryFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionReflectiveSubcategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionReflectiveSubcategoryUp.mk
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 0 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 1 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 2 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 3 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 4 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 5 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 6 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 7 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 8 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 9 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 10 ef))
      (cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEventAtDefault 11 ef)))

private theorem cauchyCompletionReflectiveSubcategory_mk_congr
    {S S' M M' J J' U U' Q Q' E E' Z Z' T T' H H' C C' P P' N N' : BHist}
    (hS : S' = S) (hM : M' = M) (hJ : J' = J) (hU : U' = U)
    (hQ : Q' = Q) (hE : E' = E) (hZ : Z' = Z) (hT : T' = T)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    CauchyCompletionReflectiveSubcategoryUp.mk S' M' J' U' Q' E' Z' T' H' C' P' N' =
      CauchyCompletionReflectiveSubcategoryUp.mk S M J U Q E Z T H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hM
  cases hJ
  cases hU
  cases hQ
  cases hE
  cases hZ
  cases hT
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionReflectiveSubcategoryUp,
      cauchyCompletionReflectiveSubcategoryFromEventFlow
        (cauchyCompletionReflectiveSubcategoryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S M J U Q E Z T H C P N =>
      exact
        congrArg some
          (cauchyCompletionReflectiveSubcategory_mk_congr
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode S)
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode M)
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode J)
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode U)
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode Q)
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode E)
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode Z)
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode T)
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode H)
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode C)
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode P)
            (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode N))

private theorem cauchyCompletionReflectiveSubcategoryToEventFlow_injective
    {x y : CauchyCompletionReflectiveSubcategoryUp} :
    cauchyCompletionReflectiveSubcategoryToEventFlow x =
      cauchyCompletionReflectiveSubcategoryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionReflectiveSubcategoryFromEventFlow
          (cauchyCompletionReflectiveSubcategoryToEventFlow x) =
        cauchyCompletionReflectiveSubcategoryFromEventFlow
          (cauchyCompletionReflectiveSubcategoryToEventFlow y) :=
    congrArg cauchyCompletionReflectiveSubcategoryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyCompletionReflectiveSubcategory_field_faithful :
    ∀ x y : CauchyCompletionReflectiveSubcategoryUp,
      cauchyCompletionReflectiveSubcategoryFields x =
        cauchyCompletionReflectiveSubcategoryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S M J U Q E Z T H C P N =>
      cases y with
      | mk S' M' J' U' Q' E' Z' T' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyCompletionReflectiveSubcategoryBHistCarrier :
    BHistCarrier CauchyCompletionReflectiveSubcategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionReflectiveSubcategoryToEventFlow
  fromEventFlow := cauchyCompletionReflectiveSubcategoryFromEventFlow

instance cauchyCompletionReflectiveSubcategoryChapterTasteGate :
    ChapterTasteGate CauchyCompletionReflectiveSubcategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionReflectiveSubcategoryFromEventFlow
        (cauchyCompletionReflectiveSubcategoryToEventFlow x) = some x
    exact CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCompletionReflectiveSubcategoryToEventFlow_injective heq)

instance cauchyCompletionReflectiveSubcategoryFieldFaithful :
    FieldFaithful CauchyCompletionReflectiveSubcategoryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyCompletionReflectiveSubcategoryFields
  field_faithful := cauchyCompletionReflectiveSubcategory_field_faithful

def taste_gate : ChapterTasteGate CauchyCompletionReflectiveSubcategoryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionReflectiveSubcategoryChapterTasteGate

theorem CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionReflectiveSubcategoryDecodeBHist
        (cauchyCompletionReflectiveSubcategoryEncodeBHist h) = h) ∧
      (∀ x : CauchyCompletionReflectiveSubcategoryUp,
        cauchyCompletionReflectiveSubcategoryFromEventFlow
          (cauchyCompletionReflectiveSubcategoryToEventFlow x) = some x) ∧
        (∀ x y : CauchyCompletionReflectiveSubcategoryUp,
          cauchyCompletionReflectiveSubcategoryToEventFlow x =
            cauchyCompletionReflectiveSubcategoryToEventFlow y → x = y) ∧
          cauchyCompletionReflectiveSubcategoryEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_decode,
      CauchyCompletionReflectiveSubcategoryTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => cauchyCompletionReflectiveSubcategoryToEventFlow_injective heq),
      rfl⟩

end TasteGate
end BEDC.Derived.CauchyCompletionReflectiveSubcategoryUp
