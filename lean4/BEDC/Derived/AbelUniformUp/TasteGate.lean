import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelUniformUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelUniformUp : Type where
  | mk (R S P W T Q E H C L N : BHist) : AbelUniformUp
  deriving DecidableEq

def abelUniformEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelUniformEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelUniformEncodeBHist h

def abelUniformDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelUniformDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelUniformDecodeBHist tail)

private theorem AbelUniformTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, abelUniformDecodeBHist (abelUniformEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def abelUniformFields : AbelUniformUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelUniformUp.mk R S P W T Q E H C L N => [R, S, P, W, T, Q, E, H, C, L, N]

def abelUniformToEventFlow : AbelUniformUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (abelUniformFields x).map abelUniformEncodeBHist

def abelUniformFromEventFlow : EventFlow → Option AbelUniformUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | S :: rest1 =>
          match rest1 with
          | [] => none
          | P :: rest2 =>
              match rest2 with
              | [] => none
              | W :: rest3 =>
                  match rest3 with
                  | [] => none
                  | T :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | C :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | L :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (AbelUniformUp.mk
                                                      (abelUniformDecodeBHist R)
                                                      (abelUniformDecodeBHist S)
                                                      (abelUniformDecodeBHist P)
                                                      (abelUniformDecodeBHist W)
                                                      (abelUniformDecodeBHist T)
                                                      (abelUniformDecodeBHist Q)
                                                      (abelUniformDecodeBHist E)
                                                      (abelUniformDecodeBHist H)
                                                      (abelUniformDecodeBHist C)
                                                      (abelUniformDecodeBHist L)
                                                      (abelUniformDecodeBHist N))
                                              | _ :: _ => none

private theorem AbelUniformTasteGate_single_carrier_alignment_round_trip :
    ∀ x : AbelUniformUp,
      abelUniformFromEventFlow (abelUniformToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S P W T Q E H C L N =>
      change
        some
          (AbelUniformUp.mk
            (abelUniformDecodeBHist (abelUniformEncodeBHist R))
            (abelUniformDecodeBHist (abelUniformEncodeBHist S))
            (abelUniformDecodeBHist (abelUniformEncodeBHist P))
            (abelUniformDecodeBHist (abelUniformEncodeBHist W))
            (abelUniformDecodeBHist (abelUniformEncodeBHist T))
            (abelUniformDecodeBHist (abelUniformEncodeBHist Q))
            (abelUniformDecodeBHist (abelUniformEncodeBHist E))
            (abelUniformDecodeBHist (abelUniformEncodeBHist H))
            (abelUniformDecodeBHist (abelUniformEncodeBHist C))
            (abelUniformDecodeBHist (abelUniformEncodeBHist L))
            (abelUniformDecodeBHist (abelUniformEncodeBHist N))) =
          some (AbelUniformUp.mk R S P W T Q E H C L N)
      rw [AbelUniformTasteGate_single_carrier_alignment_decode R,
        AbelUniformTasteGate_single_carrier_alignment_decode S,
        AbelUniformTasteGate_single_carrier_alignment_decode P,
        AbelUniformTasteGate_single_carrier_alignment_decode W,
        AbelUniformTasteGate_single_carrier_alignment_decode T,
        AbelUniformTasteGate_single_carrier_alignment_decode Q,
        AbelUniformTasteGate_single_carrier_alignment_decode E,
        AbelUniformTasteGate_single_carrier_alignment_decode H,
        AbelUniformTasteGate_single_carrier_alignment_decode C,
        AbelUniformTasteGate_single_carrier_alignment_decode L,
        AbelUniformTasteGate_single_carrier_alignment_decode N]

private theorem AbelUniformTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbelUniformUp} :
    abelUniformToEventFlow x = abelUniformToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelUniformFromEventFlow (abelUniformToEventFlow x) =
        abelUniformFromEventFlow (abelUniformToEventFlow y) :=
    congrArg abelUniformFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (AbelUniformTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbelUniformTasteGate_single_carrier_alignment_round_trip y)))

instance abelUniformBHistCarrier : BHistCarrier AbelUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelUniformToEventFlow
  fromEventFlow := abelUniformFromEventFlow

instance abelUniformChapterTasteGate : ChapterTasteGate AbelUniformUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change abelUniformFromEventFlow (abelUniformToEventFlow x) = some x
    exact AbelUniformTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbelUniformTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate AbelUniformUp :=
  -- BEDC touchpoint anchor: BHist BMark
  abelUniformChapterTasteGate

theorem AbelUniformTasteGate_single_carrier_alignment :
    (∀ h : BHist, abelUniformDecodeBHist (abelUniformEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier AbelUniformUp) ∧
        Nonempty (ChapterTasteGate AbelUniformUp) ∧
          abelUniformEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨AbelUniformTasteGate_single_carrier_alignment_decode,
      ⟨abelUniformBHistCarrier⟩,
      ⟨abelUniformChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.AbelUniformUp.TasteGate
