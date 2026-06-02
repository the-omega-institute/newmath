import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CalculusUp : Type where
  | mk (R L C D I Q H T P N : BHist) : CalculusUp
  deriving DecidableEq

def calculusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: calculusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: calculusEncodeBHist h

def calculusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (calculusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (calculusDecodeBHist tail)

private theorem CalculusTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, calculusDecodeBHist (calculusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def calculusToEventFlow : CalculusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CalculusUp.mk R L C D I Q H T P N =>
      [calculusEncodeBHist R,
        calculusEncodeBHist L,
        calculusEncodeBHist C,
        calculusEncodeBHist D,
        calculusEncodeBHist I,
        calculusEncodeBHist Q,
        calculusEncodeBHist H,
        calculusEncodeBHist T,
        calculusEncodeBHist P,
        calculusEncodeBHist N]

def calculusFromEventFlow : EventFlow → Option CalculusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: restL =>
      match restL with
      | [] => none
      | L :: restC =>
          match restC with
          | [] => none
          | C :: restD =>
              match restD with
              | [] => none
              | D :: restI =>
                  match restI with
                  | [] => none
                  | I :: restQ =>
                      match restQ with
                      | [] => none
                      | Q :: restH =>
                          match restH with
                          | [] => none
                          | H :: restT =>
                              match restT with
                              | [] => none
                              | T :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (CalculusUp.mk
                                                  (calculusDecodeBHist R)
                                                  (calculusDecodeBHist L)
                                                  (calculusDecodeBHist C)
                                                  (calculusDecodeBHist D)
                                                  (calculusDecodeBHist I)
                                                  (calculusDecodeBHist Q)
                                                  (calculusDecodeBHist H)
                                                  (calculusDecodeBHist T)
                                                  (calculusDecodeBHist P)
                                                  (calculusDecodeBHist N))
                                          | _ :: _ => none

private theorem CalculusTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CalculusUp, calculusFromEventFlow (calculusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk R L C D I Q H T P N =>
      change
        some
          (CalculusUp.mk
            (calculusDecodeBHist (calculusEncodeBHist R))
            (calculusDecodeBHist (calculusEncodeBHist L))
            (calculusDecodeBHist (calculusEncodeBHist C))
            (calculusDecodeBHist (calculusEncodeBHist D))
            (calculusDecodeBHist (calculusEncodeBHist I))
            (calculusDecodeBHist (calculusEncodeBHist Q))
            (calculusDecodeBHist (calculusEncodeBHist H))
            (calculusDecodeBHist (calculusEncodeBHist T))
            (calculusDecodeBHist (calculusEncodeBHist P))
            (calculusDecodeBHist (calculusEncodeBHist N))) =
          some (CalculusUp.mk R L C D I Q H T P N)
      rw [CalculusTasteGate_single_carrier_alignment_decode R,
        CalculusTasteGate_single_carrier_alignment_decode L,
        CalculusTasteGate_single_carrier_alignment_decode C,
        CalculusTasteGate_single_carrier_alignment_decode D,
        CalculusTasteGate_single_carrier_alignment_decode I,
        CalculusTasteGate_single_carrier_alignment_decode Q,
        CalculusTasteGate_single_carrier_alignment_decode H,
        CalculusTasteGate_single_carrier_alignment_decode T,
        CalculusTasteGate_single_carrier_alignment_decode P,
        CalculusTasteGate_single_carrier_alignment_decode N]

private theorem CalculusToEventFlow_injective {x y : CalculusUp} :
    calculusToEventFlow x = calculusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      calculusFromEventFlow (calculusToEventFlow x) =
        calculusFromEventFlow (calculusToEventFlow y) :=
    congrArg calculusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CalculusTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CalculusTasteGate_single_carrier_alignment_round_trip y)))

instance calculusBHistCarrier : BHistCarrier CalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := calculusToEventFlow
  fromEventFlow := calculusFromEventFlow

instance calculusChapterTasteGate : ChapterTasteGate CalculusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change calculusFromEventFlow (calculusToEventFlow x) = some x
    exact CalculusTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CalculusToEventFlow_injective heq)

theorem CalculusTasteGate_single_carrier_alignment :
    (∀ h : BHist, calculusDecodeBHist (calculusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CalculusUp) ∧
        Nonempty (ChapterTasteGate CalculusUp) ∧
          calculusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CalculusTasteGate_single_carrier_alignment_decode,
      ⟨calculusBHistCarrier⟩,
      ⟨calculusChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CalculusUp
