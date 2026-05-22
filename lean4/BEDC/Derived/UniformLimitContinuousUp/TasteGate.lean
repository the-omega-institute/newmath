import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformLimitContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformLimitContinuousUp : Type where
  | mk (F U M W R E H C P N : BHist) : UniformLimitContinuousUp
  deriving DecidableEq

def uniformLimitContinuousEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformLimitContinuousEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformLimitContinuousEncodeBHist h

def uniformLimitContinuousDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformLimitContinuousDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformLimitContinuousDecodeBHist tail)

private theorem UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformLimitContinuousFields : UniformLimitContinuousUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformLimitContinuousUp.mk F U M W R E H C P N => [F, U, M, W, R, E, H, C, P, N]

def uniformLimitContinuousToEventFlow : UniformLimitContinuousUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformLimitContinuousFields x).map uniformLimitContinuousEncodeBHist

def uniformLimitContinuousFromEventFlow : EventFlow → Option UniformLimitContinuousUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: restF =>
      match restF with
      | U :: restU =>
          match restU with
          | M :: restM =>
              match restM with
              | W :: restW =>
                  match restW with
                  | R :: restR =>
                      match restR with
                      | E :: restE =>
                          match restE with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: rest =>
                                          match rest with
                                          | [] =>
                                              some
                                                (UniformLimitContinuousUp.mk
                                                  (uniformLimitContinuousDecodeBHist F)
                                                  (uniformLimitContinuousDecodeBHist U)
                                                  (uniformLimitContinuousDecodeBHist M)
                                                  (uniformLimitContinuousDecodeBHist W)
                                                  (uniformLimitContinuousDecodeBHist R)
                                                  (uniformLimitContinuousDecodeBHist E)
                                                  (uniformLimitContinuousDecodeBHist H)
                                                  (uniformLimitContinuousDecodeBHist C)
                                                  (uniformLimitContinuousDecodeBHist P)
                                                  (uniformLimitContinuousDecodeBHist N))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem uniformLimitContinuous_mk_congr
    {F F' U U' M M' W W' R R' E E' H H' C C' P P' N N' : BHist}
    (hF : F' = F) (hU : U' = U) (hM : M' = M) (hW : W' = W)
    (hR : R' = R) (hE : E' = E) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    UniformLimitContinuousUp.mk F' U' M' W' R' E' H' C' P' N' =
      UniformLimitContinuousUp.mk F U M W R E H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hF
  cases hU
  cases hM
  cases hW
  cases hR
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

private theorem UniformLimitContinuousUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformLimitContinuousUp,
      uniformLimitContinuousFromEventFlow (uniformLimitContinuousToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F U M W R E H C P N =>
      exact
        congrArg some
          (uniformLimitContinuous_mk_congr
            (UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode F)
            (UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode U)
            (UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode M)
            (UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode W)
            (UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode R)
            (UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode E)
            (UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode H)
            (UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode C)
            (UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode P)
            (UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode N))

private theorem uniformLimitContinuousToEventFlow_injective
    {x y : UniformLimitContinuousUp} :
    uniformLimitContinuousToEventFlow x = uniformLimitContinuousToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformLimitContinuousFromEventFlow (uniformLimitContinuousToEventFlow x) =
        uniformLimitContinuousFromEventFlow (uniformLimitContinuousToEventFlow y) :=
    congrArg uniformLimitContinuousFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformLimitContinuousUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (UniformLimitContinuousUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem uniformLimitContinuous_field_faithful :
    ∀ x y : UniformLimitContinuousUp,
      uniformLimitContinuousFields x = uniformLimitContinuousFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F U M W R E H C P N =>
      cases y with
      | mk F' U' M' W' R' E' H' C' P' N' =>
          cases hfields
          rfl

instance uniformLimitContinuousBHistCarrier : BHistCarrier UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformLimitContinuousToEventFlow
  fromEventFlow := uniformLimitContinuousFromEventFlow

instance uniformLimitContinuousChapterTasteGate :
    ChapterTasteGate UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformLimitContinuousFromEventFlow (uniformLimitContinuousToEventFlow x) = some x
    exact UniformLimitContinuousUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformLimitContinuousToEventFlow_injective heq)

instance uniformLimitContinuousFieldFaithful : FieldFaithful UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := uniformLimitContinuousFields
  field_faithful := uniformLimitContinuous_field_faithful

instance uniformLimitContinuousNontrivial :
    BEDC.Meta.TasteGate.Nontrivial UniformLimitContinuousUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UniformLimitContinuousUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UniformLimitContinuousUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UniformLimitContinuousUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformLimitContinuousChapterTasteGate

theorem UniformLimitContinuousUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UniformLimitContinuousUp) ∧
      Nonempty (FieldFaithful UniformLimitContinuousUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial UniformLimitContinuousUp) ∧
      (∀ h : BHist,
        uniformLimitContinuousDecodeBHist (uniformLimitContinuousEncodeBHist h) = h) ∧
      (∀ x : UniformLimitContinuousUp,
        uniformLimitContinuousFromEventFlow (uniformLimitContinuousToEventFlow x) = some x) ∧
      (∀ x y : UniformLimitContinuousUp,
        uniformLimitContinuousToEventFlow x = uniformLimitContinuousToEventFlow y → x = y) ∧
      uniformLimitContinuousEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨uniformLimitContinuousChapterTasteGate⟩,
      ⟨uniformLimitContinuousFieldFaithful⟩,
      ⟨uniformLimitContinuousNontrivial⟩,
      UniformLimitContinuousUpTasteGate_single_carrier_alignment_decode,
      UniformLimitContinuousUpTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => uniformLimitContinuousToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UniformLimitContinuousUp
