import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ContractiveCauchyOrbitUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ContractiveCauchyOrbitUp : Type where
  | mk (X T I W R M K E H C P N : BHist) : ContractiveCauchyOrbitUp
  deriving DecidableEq

def contractiveCauchyOrbitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: contractiveCauchyOrbitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: contractiveCauchyOrbitEncodeBHist h

def contractiveCauchyOrbitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (contractiveCauchyOrbitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (contractiveCauchyOrbitDecodeBHist tail)

private theorem ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def contractiveCauchyOrbitFields : ContractiveCauchyOrbitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ContractiveCauchyOrbitUp.mk X T I W R M K E H C P N => [X, T, I, W, R, M, K, E, H, C, P, N]

def contractiveCauchyOrbitToEventFlow : ContractiveCauchyOrbitUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (contractiveCauchyOrbitFields x).map contractiveCauchyOrbitEncodeBHist

def contractiveCauchyOrbitFromEventFlow (ef : EventFlow) :
    Option ContractiveCauchyOrbitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | X :: restX =>
      match restX with
      | [] => none
      | T :: restT =>
          match restT with
          | [] => none
          | I :: restI =>
              match restI with
              | [] => none
              | W :: restW =>
                  match restW with
                  | [] => none
                  | R :: restR =>
                      match restR with
                      | [] => none
                      | M :: restM =>
                          match restM with
                          | [] => none
                          | K :: restK =>
                              match restK with
                              | [] => none
                              | E :: restE =>
                                  match restE with
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
                                                        (ContractiveCauchyOrbitUp.mk
                                                          (contractiveCauchyOrbitDecodeBHist X)
                                                          (contractiveCauchyOrbitDecodeBHist T)
                                                          (contractiveCauchyOrbitDecodeBHist I)
                                                          (contractiveCauchyOrbitDecodeBHist W)
                                                          (contractiveCauchyOrbitDecodeBHist R)
                                                          (contractiveCauchyOrbitDecodeBHist M)
                                                          (contractiveCauchyOrbitDecodeBHist K)
                                                          (contractiveCauchyOrbitDecodeBHist E)
                                                          (contractiveCauchyOrbitDecodeBHist H)
                                                          (contractiveCauchyOrbitDecodeBHist C)
                                                          (contractiveCauchyOrbitDecodeBHist P)
                                                          (contractiveCauchyOrbitDecodeBHist N))
                                                  | _ :: _ => none

private theorem ContractiveCauchyOrbitTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ContractiveCauchyOrbitUp,
      contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X T I W R M K E H C P N =>
      change
        some
          (ContractiveCauchyOrbitUp.mk
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist X))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist T))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist I))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist W))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist R))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist M))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist K))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist E))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist H))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist C))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist P))
            (contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist N))) =
          some (ContractiveCauchyOrbitUp.mk X T I W R M K E H C P N)
      rw [ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode X,
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode T,
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode I,
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode W,
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode R,
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode M,
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode K,
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode E,
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode H,
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode C,
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode P,
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode N]

private theorem ContractiveCauchyOrbitTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ContractiveCauchyOrbitUp} :
    contractiveCauchyOrbitToEventFlow x = contractiveCauchyOrbitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow x) =
        contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow y) :=
    congrArg contractiveCauchyOrbitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ContractiveCauchyOrbitTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ContractiveCauchyOrbitTasteGate_single_carrier_alignment_round_trip y)))

instance contractiveCauchyOrbitBHistCarrier : BHistCarrier ContractiveCauchyOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := contractiveCauchyOrbitToEventFlow
  fromEventFlow := contractiveCauchyOrbitFromEventFlow

instance contractiveCauchyOrbitChapterTasteGate :
    ChapterTasteGate ContractiveCauchyOrbitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow x) =
      some x
    exact ContractiveCauchyOrbitTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ContractiveCauchyOrbitTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ContractiveCauchyOrbitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  contractiveCauchyOrbitChapterTasteGate

theorem ContractiveCauchyOrbitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      contractiveCauchyOrbitDecodeBHist (contractiveCauchyOrbitEncodeBHist h) = h) ∧
      (∀ x : ContractiveCauchyOrbitUp,
        contractiveCauchyOrbitFromEventFlow (contractiveCauchyOrbitToEventFlow x) =
          some x) ∧
        (∀ x y : ContractiveCauchyOrbitUp,
          contractiveCauchyOrbitToEventFlow x = contractiveCauchyOrbitToEventFlow y →
            x = y) ∧
          contractiveCauchyOrbitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ContractiveCauchyOrbitTasteGate_single_carrier_alignment_decode,
      ContractiveCauchyOrbitTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ContractiveCauchyOrbitTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ContractiveCauchyOrbitUp.TasteGate
