import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyMinUp : Type where
  | mk (A B W DA DB J S R E H C P N : BHist) : RegularCauchyMinUp
  deriving DecidableEq

def regularCauchyMinFields : RegularCauchyMinUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMinUp.mk A B W DA DB J S R E H C P N =>
      [A, B, W, DA, DB, J, S, R, E, H, C, P, N]

def regularCauchyMinEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyMinEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyMinEncodeBHist h

def regularCauchyMinDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyMinDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyMinDecodeBHist tail)

theorem RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist :
    forall h : BHist, regularCauchyMinDecodeBHist (regularCauchyMinEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

theorem RegularCauchyMinTasteGate_single_carrier_alignment_mk_congr
    {A1 A2 B1 B2 W1 W2 DA1 DA2 DB1 DB2 J1 J2 S1 S2 R1 R2 E1 E2 H1 H2 C1 C2 P1 P2
      N1 N2 : BHist}
    (hA : A1 = A2) (hB : B1 = B2) (hW : W1 = W2) (hDA : DA1 = DA2)
    (hDB : DB1 = DB2) (hJ : J1 = J2) (hS : S1 = S2) (hR : R1 = R2)
    (hE : E1 = E2) (hH : H1 = H2) (hC : C1 = C2) (hP : P1 = P2)
    (hN : N1 = N2) :
    RegularCauchyMinUp.mk A1 B1 W1 DA1 DB1 J1 S1 R1 E1 H1 C1 P1 N1 =
      RegularCauchyMinUp.mk A2 B2 W2 DA2 DB2 J2 S2 R2 E2 H2 C2 P2 N2 := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hB
  cases hW
  cases hDA
  cases hDB
  cases hJ
  cases hS
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def regularCauchyMinToEventFlow : RegularCauchyMinUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMinUp.mk A B W DA DB J S R E H C P N =>
      [regularCauchyMinEncodeBHist A, regularCauchyMinEncodeBHist B,
        regularCauchyMinEncodeBHist W, regularCauchyMinEncodeBHist DA,
        regularCauchyMinEncodeBHist DB, regularCauchyMinEncodeBHist J,
        regularCauchyMinEncodeBHist S, regularCauchyMinEncodeBHist R,
        regularCauchyMinEncodeBHist E, regularCauchyMinEncodeBHist H,
        regularCauchyMinEncodeBHist C, regularCauchyMinEncodeBHist P,
        regularCauchyMinEncodeBHist N]

private def regularCauchyMinEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyMinEventAtDefault index rest

def regularCauchyMinFromEventFlow (ef : EventFlow) : Option RegularCauchyMinUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyMinUp.mk
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 0 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 1 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 2 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 3 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 4 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 5 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 6 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 7 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 8 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 9 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 10 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 11 ef))
      (regularCauchyMinDecodeBHist (regularCauchyMinEventAtDefault 12 ef)))

theorem RegularCauchyMinTasteGate_single_carrier_alignment_round_trip :
    forall x : RegularCauchyMinUp,
      regularCauchyMinFromEventFlow (regularCauchyMinToEventFlow x) = some x
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyMinUp.mk A B W DA DB J S R E H C P N =>
      congrArg some
        (RegularCauchyMinTasteGate_single_carrier_alignment_mk_congr
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist A)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist B)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist W)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist DA)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist DB)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist J)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist S)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist R)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist E)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist H)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist C)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist P)
          (RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist N))

theorem RegularCauchyMinTasteGate_single_carrier_alignment_toEventFlow_injective {x y : RegularCauchyMinUp} :
    regularCauchyMinToEventFlow x = regularCauchyMinToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyMinFromEventFlow (regularCauchyMinToEventFlow x) =
        regularCauchyMinFromEventFlow (regularCauchyMinToEventFlow y) :=
    congrArg regularCauchyMinFromEventFlow heq
  have hsome : some x = some y :=
    Eq.trans (RegularCauchyMinTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RegularCauchyMinTasteGate_single_carrier_alignment_round_trip y))
  cases hsome
  rfl

instance regularCauchyMinBHistCarrier : BHistCarrier RegularCauchyMinUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyMinToEventFlow
  fromEventFlow := regularCauchyMinFromEventFlow

instance regularCauchyMinChapterTasteGate : ChapterTasteGate RegularCauchyMinUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyMinFromEventFlow (regularCauchyMinToEventFlow x) = some x
    exact RegularCauchyMinTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyMinTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyMinFieldFaithful : FieldFaithful RegularCauchyMinUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyMinFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk A₁ B₁ W₁ DA₁ DB₁ J₁ S₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk A₂ B₂ W₂ DA₂ DB₂ J₂ S₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
            injection hfields with hA t0
            injection t0 with hB t1
            injection t1 with hW t2
            injection t2 with hDA t3
            injection t3 with hDB t4
            injection t4 with hJ t5
            injection t5 with hS t6
            injection t6 with hR t7
            injection t7 with hE t8
            injection t8 with hH t9
            injection t9 with hC t10
            injection t10 with hP t11
            injection t11 with hN _
            subst hA
            subst hB
            subst hW
            subst hDA
            subst hDB
            subst hJ
            subst hS
            subst hR
            subst hE
            subst hH
            subst hC
            subst hP
            subst hN
            rfl

def taste_gate : ChapterTasteGate RegularCauchyMinUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyMinChapterTasteGate

theorem RegularCauchyMinTasteGate_single_carrier_alignment :
    (forall h : BHist, regularCauchyMinDecodeBHist (regularCauchyMinEncodeBHist h) = h) ∧
      (forall x : RegularCauchyMinUp,
        regularCauchyMinFromEventFlow (regularCauchyMinToEventFlow x) = some x) ∧
      (forall x y : RegularCauchyMinUp,
        regularCauchyMinToEventFlow x = regularCauchyMinToEventFlow y -> x = y) ∧
      regularCauchyMinEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegularCauchyMinTasteGate_single_carrier_alignment_decode_encode_bhist
  · constructor
    · exact RegularCauchyMinTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact RegularCauchyMinTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.RegularCauchyMinUp
