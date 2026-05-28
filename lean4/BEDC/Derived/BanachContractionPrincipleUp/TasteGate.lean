import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachContractionPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachContractionPrincipleUp : Type where
  | mk (M F I Q E U H C P N : BHist) : BanachContractionPrincipleUp
  deriving DecidableEq

def banachContractionPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachContractionPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachContractionPrincipleEncodeBHist h

def banachContractionPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachContractionPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachContractionPrincipleDecodeBHist tail)

private theorem BanachContractionPrincipleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      banachContractionPrincipleDecodeBHist (banachContractionPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachContractionPrincipleFields : BanachContractionPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BanachContractionPrincipleUp.mk M F I Q E U H C P N => [M, F, I, Q, E, U, H, C, P, N]

def banachContractionPrincipleToEventFlow : BanachContractionPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BanachContractionPrincipleUp.mk M F I Q E U H C P N =>
      [banachContractionPrincipleEncodeBHist M,
        banachContractionPrincipleEncodeBHist F,
        banachContractionPrincipleEncodeBHist I,
        banachContractionPrincipleEncodeBHist Q,
        banachContractionPrincipleEncodeBHist E,
        banachContractionPrincipleEncodeBHist U,
        banachContractionPrincipleEncodeBHist H,
        banachContractionPrincipleEncodeBHist C,
        banachContractionPrincipleEncodeBHist P,
        banachContractionPrincipleEncodeBHist N]

def banachContractionPrincipleFromEventFlow :
    EventFlow → Option BanachContractionPrincipleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | M :: restF =>
      match restF with
      | [] => none
      | F :: restI =>
          match restI with
          | [] => none
          | I :: restQ =>
              match restQ with
              | [] => none
              | Q :: restE =>
                  match restE with
                  | [] => none
                  | E :: restU =>
                      match restU with
                      | [] => none
                      | U :: restH =>
                          match restH with
                          | [] => none
                          | H :: restC =>
                              match restC with
                              | [] => none
                              | C :: restP =>
                                  match restP with
                                  | [] => none
                                  | P :: restN =>
                                      match restN with
                                      | [] => none
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (BanachContractionPrincipleUp.mk
                                                  (banachContractionPrincipleDecodeBHist M)
                                                  (banachContractionPrincipleDecodeBHist F)
                                                  (banachContractionPrincipleDecodeBHist I)
                                                  (banachContractionPrincipleDecodeBHist Q)
                                                  (banachContractionPrincipleDecodeBHist E)
                                                  (banachContractionPrincipleDecodeBHist U)
                                                  (banachContractionPrincipleDecodeBHist H)
                                                  (banachContractionPrincipleDecodeBHist C)
                                                  (banachContractionPrincipleDecodeBHist P)
                                                  (banachContractionPrincipleDecodeBHist N))
                                          | _ :: _ => none

private theorem BanachContractionPrincipleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BanachContractionPrincipleUp,
      banachContractionPrincipleFromEventFlow (banachContractionPrincipleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk M F I Q E U H C P N =>
      change
        some
          (BanachContractionPrincipleUp.mk
            (banachContractionPrincipleDecodeBHist (banachContractionPrincipleEncodeBHist M))
            (banachContractionPrincipleDecodeBHist (banachContractionPrincipleEncodeBHist F))
            (banachContractionPrincipleDecodeBHist (banachContractionPrincipleEncodeBHist I))
            (banachContractionPrincipleDecodeBHist (banachContractionPrincipleEncodeBHist Q))
            (banachContractionPrincipleDecodeBHist (banachContractionPrincipleEncodeBHist E))
            (banachContractionPrincipleDecodeBHist (banachContractionPrincipleEncodeBHist U))
            (banachContractionPrincipleDecodeBHist (banachContractionPrincipleEncodeBHist H))
            (banachContractionPrincipleDecodeBHist (banachContractionPrincipleEncodeBHist C))
            (banachContractionPrincipleDecodeBHist (banachContractionPrincipleEncodeBHist P))
            (banachContractionPrincipleDecodeBHist (banachContractionPrincipleEncodeBHist N))) =
          some (BanachContractionPrincipleUp.mk M F I Q E U H C P N)
      rw [BanachContractionPrincipleTasteGate_single_carrier_alignment_decode M,
        BanachContractionPrincipleTasteGate_single_carrier_alignment_decode F,
        BanachContractionPrincipleTasteGate_single_carrier_alignment_decode I,
        BanachContractionPrincipleTasteGate_single_carrier_alignment_decode Q,
        BanachContractionPrincipleTasteGate_single_carrier_alignment_decode E,
        BanachContractionPrincipleTasteGate_single_carrier_alignment_decode U,
        BanachContractionPrincipleTasteGate_single_carrier_alignment_decode H,
        BanachContractionPrincipleTasteGate_single_carrier_alignment_decode C,
        BanachContractionPrincipleTasteGate_single_carrier_alignment_decode P,
        BanachContractionPrincipleTasteGate_single_carrier_alignment_decode N]

private theorem BanachContractionPrincipleToEventFlow_injective
    {x y : BanachContractionPrincipleUp} :
    banachContractionPrincipleToEventFlow x =
        banachContractionPrincipleToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachContractionPrincipleFromEventFlow (banachContractionPrincipleToEventFlow x) =
        banachContractionPrincipleFromEventFlow (banachContractionPrincipleToEventFlow y) :=
    congrArg banachContractionPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BanachContractionPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BanachContractionPrincipleTasteGate_single_carrier_alignment_round_trip y)))

instance banachContractionPrincipleBHistCarrier :
    BHistCarrier BanachContractionPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachContractionPrincipleToEventFlow
  fromEventFlow := banachContractionPrincipleFromEventFlow

instance banachContractionPrincipleChapterTasteGate :
    ChapterTasteGate BanachContractionPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      banachContractionPrincipleFromEventFlow (banachContractionPrincipleToEventFlow x) =
        some x
    exact BanachContractionPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BanachContractionPrincipleToEventFlow_injective heq)

theorem BanachContractionPrincipleTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier BanachContractionPrincipleUp) ∧
      Nonempty (ChapterTasteGate BanachContractionPrincipleUp) ∧
        (∀ x : BanachContractionPrincipleUp,
          banachContractionPrincipleFromEventFlow
              (banachContractionPrincipleToEventFlow x) = some x) ∧
          banachContractionPrincipleEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨banachContractionPrincipleBHistCarrier⟩,
      ⟨banachContractionPrincipleChapterTasteGate⟩,
      BanachContractionPrincipleTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.BanachContractionPrincipleUp
