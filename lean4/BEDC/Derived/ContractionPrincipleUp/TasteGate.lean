import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContractionPrincipleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContractionPrincipleUp : Type where
  | mk (X d T q I L H C P N : BHist) : ContractionPrincipleUp
  deriving DecidableEq

def contractionPrincipleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contractionPrincipleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contractionPrincipleEncodeBHist h

def contractionPrincipleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contractionPrincipleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contractionPrincipleDecodeBHist tail)

private theorem ContractionPrincipleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contractionPrincipleFields : ContractionPrincipleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContractionPrincipleUp.mk X d T q I L H C P N => [X, d, T, q, I, L, H, C, P, N]

def contractionPrincipleToEventFlow : ContractionPrincipleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map contractionPrincipleEncodeBHist (contractionPrincipleFields x)

def contractionPrincipleFromEventFlow : EventFlow → Option ContractionPrincipleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: restD =>
      match restD with
      | [] => none
      | d :: restT =>
          match restT with
          | [] => none
          | T :: restQ =>
              match restQ with
              | [] => none
              | q :: restI =>
                  match restI with
                  | [] => none
                  | I :: restL =>
                      match restL with
                      | [] => none
                      | L :: restH =>
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
                                                (ContractionPrincipleUp.mk
                                                  (contractionPrincipleDecodeBHist X)
                                                  (contractionPrincipleDecodeBHist d)
                                                  (contractionPrincipleDecodeBHist T)
                                                  (contractionPrincipleDecodeBHist q)
                                                  (contractionPrincipleDecodeBHist I)
                                                  (contractionPrincipleDecodeBHist L)
                                                  (contractionPrincipleDecodeBHist H)
                                                  (contractionPrincipleDecodeBHist C)
                                                  (contractionPrincipleDecodeBHist P)
                                                  (contractionPrincipleDecodeBHist N))
                                          | _ :: _ => none

private theorem ContractionPrincipleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContractionPrincipleUp,
      contractionPrincipleFromEventFlow (contractionPrincipleToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X d T q I L H C P N =>
      change
        some
          (ContractionPrincipleUp.mk
            (contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist X))
            (contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist d))
            (contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist T))
            (contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist q))
            (contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist I))
            (contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist L))
            (contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist H))
            (contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist C))
            (contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist P))
            (contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist N))) =
          some (ContractionPrincipleUp.mk X d T q I L H C P N)
      rw [ContractionPrincipleTasteGate_single_carrier_alignment_decode X,
        ContractionPrincipleTasteGate_single_carrier_alignment_decode d,
        ContractionPrincipleTasteGate_single_carrier_alignment_decode T,
        ContractionPrincipleTasteGate_single_carrier_alignment_decode q,
        ContractionPrincipleTasteGate_single_carrier_alignment_decode I,
        ContractionPrincipleTasteGate_single_carrier_alignment_decode L,
        ContractionPrincipleTasteGate_single_carrier_alignment_decode H,
        ContractionPrincipleTasteGate_single_carrier_alignment_decode C,
        ContractionPrincipleTasteGate_single_carrier_alignment_decode P,
        ContractionPrincipleTasteGate_single_carrier_alignment_decode N]

private theorem ContractionPrincipleToEventFlow_injective {x y : ContractionPrincipleUp} :
    contractionPrincipleToEventFlow x = contractionPrincipleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contractionPrincipleFromEventFlow (contractionPrincipleToEventFlow x) =
        contractionPrincipleFromEventFlow (contractionPrincipleToEventFlow y) :=
    congrArg contractionPrincipleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ContractionPrincipleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContractionPrincipleTasteGate_single_carrier_alignment_round_trip y)))

instance contractionPrincipleBHistCarrier : BHistCarrier ContractionPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contractionPrincipleToEventFlow
  fromEventFlow := contractionPrincipleFromEventFlow

instance contractionPrincipleChapterTasteGate :
    ChapterTasteGate ContractionPrincipleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contractionPrincipleFromEventFlow (contractionPrincipleToEventFlow x) = some x
    exact ContractionPrincipleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ContractionPrincipleToEventFlow_injective heq)

theorem ContractionPrincipleTasteGate_single_carrier_alignment :
    (∀ h : BHist, contractionPrincipleDecodeBHist (contractionPrincipleEncodeBHist h) = h) ∧
      (∀ x : ContractionPrincipleUp,
        contractionPrincipleFromEventFlow (contractionPrincipleToEventFlow x) = some x) ∧
        (∀ x y : ContractionPrincipleUp,
          contractionPrincipleToEventFlow x = contractionPrincipleToEventFlow y → x = y) ∧
          contractionPrincipleEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ContractionPrincipleTasteGate_single_carrier_alignment_decode,
      ContractionPrincipleTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ h => ContractionPrincipleToEventFlow_injective h),
      rfl⟩

end BEDC.Derived.ContractionPrincipleUp
