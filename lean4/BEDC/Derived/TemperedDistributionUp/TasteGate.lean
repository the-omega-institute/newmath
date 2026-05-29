import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TemperedDistributionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TemperedDistributionUp : Type where
  | mk (S G A F W Q E L H C P N : BHist) : TemperedDistributionUp
  deriving DecidableEq

def temperedDistributionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: temperedDistributionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: temperedDistributionEncodeBHist h

def temperedDistributionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (temperedDistributionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (temperedDistributionDecodeBHist tail)

private theorem TemperedDistributionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      temperedDistributionDecodeBHist (temperedDistributionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def temperedDistributionFields : TemperedDistributionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TemperedDistributionUp.mk S G A F W Q E L H C P N => [S, G, A, F, W, Q, E, L, H, C, P, N]

def temperedDistributionToEventFlow : TemperedDistributionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map temperedDistributionEncodeBHist (temperedDistributionFields x)

def temperedDistributionFromEventFlow : EventFlow → Option TemperedDistributionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: restS =>
      match restS with
      | [] => none
      | G :: restG =>
          match restG with
          | [] => none
          | A :: restA =>
              match restA with
              | [] => none
              | F :: restF =>
                  match restF with
                  | [] => none
                  | W :: restW =>
                      match restW with
                      | [] => none
                      | Q :: restQ =>
                          match restQ with
                          | [] => none
                          | E :: restE =>
                              match restE with
                              | [] => none
                              | L :: restL =>
                                  match restL with
                                  | [] => none
                                  | H :: restH =>
                                      match restH with
                                      | [] => none
                                      | C :: restC =>
                                          match restC with
                                          | [] => none
                                          | P :: restP =>
                                              match restP with
                                              | [] => none
                                              | N :: restN =>
                                                  match restN with
                                                  | [] =>
                                                      some
                                                        (TemperedDistributionUp.mk
                                                          (temperedDistributionDecodeBHist S)
                                                          (temperedDistributionDecodeBHist G)
                                                          (temperedDistributionDecodeBHist A)
                                                          (temperedDistributionDecodeBHist F)
                                                          (temperedDistributionDecodeBHist W)
                                                          (temperedDistributionDecodeBHist Q)
                                                          (temperedDistributionDecodeBHist E)
                                                          (temperedDistributionDecodeBHist L)
                                                          (temperedDistributionDecodeBHist H)
                                                          (temperedDistributionDecodeBHist C)
                                                          (temperedDistributionDecodeBHist P)
                                                          (temperedDistributionDecodeBHist N))
                                                  | _ :: _ => none

private theorem TemperedDistributionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TemperedDistributionUp,
      temperedDistributionFromEventFlow (temperedDistributionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S G A F W Q E L H C P N =>
      change
        some
          (TemperedDistributionUp.mk
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist S))
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist G))
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist A))
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist F))
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist W))
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist Q))
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist E))
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist L))
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist H))
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist C))
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist P))
            (temperedDistributionDecodeBHist (temperedDistributionEncodeBHist N))) =
          some (TemperedDistributionUp.mk S G A F W Q E L H C P N)
      rw [TemperedDistributionTasteGate_single_carrier_alignment_decode S,
        TemperedDistributionTasteGate_single_carrier_alignment_decode G,
        TemperedDistributionTasteGate_single_carrier_alignment_decode A,
        TemperedDistributionTasteGate_single_carrier_alignment_decode F,
        TemperedDistributionTasteGate_single_carrier_alignment_decode W,
        TemperedDistributionTasteGate_single_carrier_alignment_decode Q,
        TemperedDistributionTasteGate_single_carrier_alignment_decode E,
        TemperedDistributionTasteGate_single_carrier_alignment_decode L,
        TemperedDistributionTasteGate_single_carrier_alignment_decode H,
        TemperedDistributionTasteGate_single_carrier_alignment_decode C,
        TemperedDistributionTasteGate_single_carrier_alignment_decode P,
        TemperedDistributionTasteGate_single_carrier_alignment_decode N]

private theorem TemperedDistributionTasteGate_single_carrier_alignment_injective
    {x y : TemperedDistributionUp} :
    temperedDistributionToEventFlow x = temperedDistributionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      temperedDistributionFromEventFlow (temperedDistributionToEventFlow x) =
        temperedDistributionFromEventFlow (temperedDistributionToEventFlow y) :=
    congrArg temperedDistributionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TemperedDistributionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TemperedDistributionTasteGate_single_carrier_alignment_round_trip y)))

instance temperedDistributionBHistCarrier : BHistCarrier TemperedDistributionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := temperedDistributionToEventFlow
  fromEventFlow := temperedDistributionFromEventFlow

instance temperedDistributionChapterTasteGate : ChapterTasteGate TemperedDistributionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change temperedDistributionFromEventFlow (temperedDistributionToEventFlow x) = some x
    exact TemperedDistributionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TemperedDistributionTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate TemperedDistributionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  temperedDistributionChapterTasteGate

theorem TemperedDistributionTasteGate_single_carrier_alignment :
    (∀ h : BHist, temperedDistributionDecodeBHist (temperedDistributionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier TemperedDistributionUp) ∧
        Nonempty (ChapterTasteGate TemperedDistributionUp) ∧
          temperedDistributionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨TemperedDistributionTasteGate_single_carrier_alignment_decode,
      ⟨temperedDistributionBHistCarrier⟩,
      ⟨temperedDistributionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.TemperedDistributionUp
