import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyDiagonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyDiagonalUp : Type where
  | mk (Q S R L W P N : BHist) : RegularCauchyDiagonalUp
  deriving DecidableEq

def regularCauchyDiagonalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyDiagonalEncodeBHist h

def regularCauchyDiagonalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyDiagonalDecodeBHist tail)

private theorem regularCauchyDiagonal_decode_encode :
    ∀ h : BHist,
      regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyDiagonalFields : RegularCauchyDiagonalUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyDiagonalUp.mk Q S R L W P N => [Q, S, R, L, W, P, N]

def regularCauchyDiagonalToEventFlow : RegularCauchyDiagonalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyDiagonalUp.mk Q S R L W P N =>
      [regularCauchyDiagonalEncodeBHist Q,
        regularCauchyDiagonalEncodeBHist S,
        regularCauchyDiagonalEncodeBHist R,
        regularCauchyDiagonalEncodeBHist L,
        regularCauchyDiagonalEncodeBHist W,
        regularCauchyDiagonalEncodeBHist P,
        regularCauchyDiagonalEncodeBHist N]

def regularCauchyDiagonalFromEventFlow :
    EventFlow → Option RegularCauchyDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => none
  | _Q :: [] => none
  | _Q :: _S :: [] => none
  | _Q :: _S :: _R :: [] => none
  | _Q :: _S :: _R :: _L :: [] => none
  | _Q :: _S :: _R :: _L :: _W :: [] => none
  | _Q :: _S :: _R :: _L :: _W :: _P :: [] => none
  | Q :: S :: R :: L :: W :: P :: N :: [] =>
      some
        (RegularCauchyDiagonalUp.mk
          (regularCauchyDiagonalDecodeBHist Q)
          (regularCauchyDiagonalDecodeBHist S)
          (regularCauchyDiagonalDecodeBHist R)
          (regularCauchyDiagonalDecodeBHist L)
          (regularCauchyDiagonalDecodeBHist W)
          (regularCauchyDiagonalDecodeBHist P)
          (regularCauchyDiagonalDecodeBHist N))
  | _Q :: _S :: _R :: _L :: _W :: _P :: _N :: _extra :: _rest => none

private theorem regularCauchyDiagonal_round_trip :
    ∀ x : RegularCauchyDiagonalUp,
      regularCauchyDiagonalFromEventFlow (regularCauchyDiagonalToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q S R L W P N =>
      exact
        Eq.trans
          (congrArg
            (fun z =>
              some
                (RegularCauchyDiagonalUp.mk z
                  (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist S))
                  (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist R))
                  (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist L))
                  (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist W))
                  (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist P))
                  (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist N))))
            (regularCauchyDiagonal_decode_encode Q))
          (Eq.trans
            (congrArg
              (fun z =>
                some
                  (RegularCauchyDiagonalUp.mk Q z
                    (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist R))
                    (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist L))
                    (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist W))
                    (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist P))
                    (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist N))))
              (regularCauchyDiagonal_decode_encode S))
            (Eq.trans
              (congrArg
                (fun z =>
                  some
                    (RegularCauchyDiagonalUp.mk Q S z
                      (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist L))
                      (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist W))
                      (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist P))
                      (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist N))))
                (regularCauchyDiagonal_decode_encode R))
              (Eq.trans
                (congrArg
                  (fun z =>
                    some
                      (RegularCauchyDiagonalUp.mk Q S R z
                        (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist W))
                        (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist P))
                        (regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist N))))
                  (regularCauchyDiagonal_decode_encode L))
                (Eq.trans
                  (congrArg
                    (fun z =>
                      some
                        (RegularCauchyDiagonalUp.mk Q S R L z
                          (regularCauchyDiagonalDecodeBHist
                            (regularCauchyDiagonalEncodeBHist P))
                          (regularCauchyDiagonalDecodeBHist
                            (regularCauchyDiagonalEncodeBHist N))))
                    (regularCauchyDiagonal_decode_encode W))
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        some
                          (RegularCauchyDiagonalUp.mk Q S R L W z
                            (regularCauchyDiagonalDecodeBHist
                              (regularCauchyDiagonalEncodeBHist N))))
                      (regularCauchyDiagonal_decode_encode P))
                    (congrArg
                      (fun z => some (RegularCauchyDiagonalUp.mk Q S R L W P z))
                      (regularCauchyDiagonal_decode_encode N)))))))

private theorem regularCauchyDiagonalEncodeBHist_injective {a b : BHist} :
    regularCauchyDiagonalEncodeBHist a = regularCauchyDiagonalEncodeBHist b → a = b := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  exact Eq.trans (regularCauchyDiagonal_decode_encode a).symm
    (Eq.trans (congrArg regularCauchyDiagonalDecodeBHist h)
      (regularCauchyDiagonal_decode_encode b))

private theorem regularCauchyDiagonalToEventFlow_injective
    {x y : RegularCauchyDiagonalUp} :
    regularCauchyDiagonalToEventFlow x = regularCauchyDiagonalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hx :
      regularCauchyDiagonalFromEventFlow (regularCauchyDiagonalToEventFlow x) =
        some x :=
    regularCauchyDiagonal_round_trip x
  have hy :
      regularCauchyDiagonalFromEventFlow (regularCauchyDiagonalToEventFlow y) =
        some y :=
    regularCauchyDiagonal_round_trip y
  have hflow :
      regularCauchyDiagonalFromEventFlow (regularCauchyDiagonalToEventFlow x) =
        regularCauchyDiagonalFromEventFlow (regularCauchyDiagonalToEventFlow y) :=
    congrArg regularCauchyDiagonalFromEventFlow hxy
  have hsome : some x = some y := Eq.trans hx.symm (Eq.trans hflow hy)
  cases hsome
  rfl

private theorem regularCauchyDiagonal_field_faithful :
    ∀ x y : RegularCauchyDiagonalUp,
      regularCauchyDiagonalFields x = regularCauchyDiagonalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk Q1 S1 R1 L1 W1 P1 N1 =>
      cases y with
      | mk Q2 S2 R2 L2 W2 P2 N2 =>
          cases h
          rfl

instance regularCauchyDiagonalBHistCarrier : BHistCarrier RegularCauchyDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyDiagonalToEventFlow
  fromEventFlow := regularCauchyDiagonalFromEventFlow

instance regularCauchyDiagonalChapterTasteGate :
    ChapterTasteGate RegularCauchyDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyDiagonalFromEventFlow (regularCauchyDiagonalToEventFlow x) = some x
    exact regularCauchyDiagonal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyDiagonalToEventFlow_injective heq)

instance regularCauchyDiagonalFieldFaithful : FieldFaithful RegularCauchyDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyDiagonalFields
  field_faithful := regularCauchyDiagonal_field_faithful

instance regularCauchyDiagonalNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyDiagonalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyDiagonalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyDiagonalChapterTasteGate

theorem RegularCauchyDiagonalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyDiagonalDecodeBHist (regularCauchyDiagonalEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyDiagonalUp,
        regularCauchyDiagonalFromEventFlow (regularCauchyDiagonalToEventFlow x) = some x) ∧
      (∀ x y : RegularCauchyDiagonalUp,
        regularCauchyDiagonalToEventFlow x = regularCauchyDiagonalToEventFlow y → x = y) ∧
      regularCauchyDiagonalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyDiagonal_decode_encode,
      regularCauchyDiagonal_round_trip,
      fun x y hxy => regularCauchyDiagonalToEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.RegularCauchyDiagonalUp
