import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SternBrocotUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SternBrocotUp : Type where
  | mk (A L U M F B Q R H C P N : BHist) : SternBrocotUp
  deriving DecidableEq

def sternBrocotEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sternBrocotEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sternBrocotEncodeBHist h

def sternBrocotDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sternBrocotDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sternBrocotDecodeBHist tail)

private theorem SternBrocotTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, sternBrocotDecodeBHist (sternBrocotEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sternBrocotFields : SternBrocotUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SternBrocotUp.mk A L U M F B Q R H C P N => [A, L, U, M, F, B, Q, R, H, C, P, N]

def sternBrocotToEventFlow : SternBrocotUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map sternBrocotEncodeBHist (sternBrocotFields x)

def sternBrocotFromEventFlow (ef : EventFlow) : Option SternBrocotUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | A :: restA =>
      match restA with
      | [] => none
      | L :: restL =>
          match restL with
          | [] => none
          | U :: restU =>
              match restU with
              | [] => none
              | M :: restM =>
                  match restM with
                  | [] => none
                  | F :: restF =>
                      match restF with
                      | [] => none
                      | B :: restB =>
                          match restB with
                          | [] => none
                          | Q :: restQ =>
                              match restQ with
                              | [] => none
                              | R :: restR =>
                                  match restR with
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
                                                        (SternBrocotUp.mk
                                                          (sternBrocotDecodeBHist A)
                                                          (sternBrocotDecodeBHist L)
                                                          (sternBrocotDecodeBHist U)
                                                          (sternBrocotDecodeBHist M)
                                                          (sternBrocotDecodeBHist F)
                                                          (sternBrocotDecodeBHist B)
                                                          (sternBrocotDecodeBHist Q)
                                                          (sternBrocotDecodeBHist R)
                                                          (sternBrocotDecodeBHist H)
                                                          (sternBrocotDecodeBHist C)
                                                          (sternBrocotDecodeBHist P)
                                                          (sternBrocotDecodeBHist N))
                                                  | _ :: _ => none

private theorem SternBrocotTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SternBrocotUp, sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A L U M F B Q R H C P N =>
      change
        some
          (SternBrocotUp.mk
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist A))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist L))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist U))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist M))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist F))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist B))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist Q))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist R))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist H))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist C))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist P))
            (sternBrocotDecodeBHist (sternBrocotEncodeBHist N))) =
          some (SternBrocotUp.mk A L U M F B Q R H C P N)
      rw [SternBrocotTasteGate_single_carrier_alignment_decode A,
        SternBrocotTasteGate_single_carrier_alignment_decode L,
        SternBrocotTasteGate_single_carrier_alignment_decode U,
        SternBrocotTasteGate_single_carrier_alignment_decode M,
        SternBrocotTasteGate_single_carrier_alignment_decode F,
        SternBrocotTasteGate_single_carrier_alignment_decode B,
        SternBrocotTasteGate_single_carrier_alignment_decode Q,
        SternBrocotTasteGate_single_carrier_alignment_decode R,
        SternBrocotTasteGate_single_carrier_alignment_decode H,
        SternBrocotTasteGate_single_carrier_alignment_decode C,
        SternBrocotTasteGate_single_carrier_alignment_decode P,
        SternBrocotTasteGate_single_carrier_alignment_decode N]

private theorem SternBrocotTasteGate_single_carrier_alignment_injective
    {x y : SternBrocotUp} :
    sternBrocotToEventFlow x = sternBrocotToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sternBrocotFromEventFlow (sternBrocotToEventFlow x) =
        sternBrocotFromEventFlow (sternBrocotToEventFlow y) :=
    congrArg sternBrocotFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SternBrocotTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SternBrocotTasteGate_single_carrier_alignment_round_trip y)))

instance sternBrocotBHistCarrier : BHistCarrier SternBrocotUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sternBrocotToEventFlow
  fromEventFlow := sternBrocotFromEventFlow

instance sternBrocotChapterTasteGate : ChapterTasteGate SternBrocotUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x
    exact SternBrocotTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SternBrocotTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate SternBrocotUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sternBrocotChapterTasteGate

theorem SternBrocotTasteGate_single_carrier_alignment :
    (∀ h : BHist, sternBrocotDecodeBHist (sternBrocotEncodeBHist h) = h) ∧
      (∀ x : SternBrocotUp, sternBrocotFromEventFlow (sternBrocotToEventFlow x) = some x) ∧
        (∀ x y : SternBrocotUp, sternBrocotToEventFlow x = sternBrocotToEventFlow y → x = y) ∧
          sternBrocotEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨SternBrocotTasteGate_single_carrier_alignment_decode,
      SternBrocotTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ h => SternBrocotTasteGate_single_carrier_alignment_injective h),
      rfl⟩

end BEDC.Derived.SternBrocotUp.TasteGate

namespace BEDC.Derived.SternBrocotUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow

theorem SternBrocotTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      TasteGate.sternBrocotDecodeBHist (TasteGate.sternBrocotEncodeBHist h) = h) ∧
      (∀ x : TasteGate.SternBrocotUp,
        TasteGate.sternBrocotFromEventFlow
          (TasteGate.sternBrocotToEventFlow x) = some x) ∧
        (∀ x y : TasteGate.SternBrocotUp,
          TasteGate.sternBrocotToEventFlow x = TasteGate.sternBrocotToEventFlow y → x = y) ∧
          TasteGate.sternBrocotEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact TasteGate.SternBrocotTasteGate_single_carrier_alignment

end BEDC.Derived.SternBrocotUp
