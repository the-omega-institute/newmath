import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UseProcessBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UseProcessBoundaryUp : Type where
  | mk (U P R E H C K N : BHist) : UseProcessBoundaryUp
  deriving DecidableEq

def useProcessBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: useProcessBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: useProcessBoundaryEncodeBHist h

def useProcessBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (useProcessBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (useProcessBoundaryDecodeBHist tail)

private theorem useProcessBoundary_decode_encode_bhist :
    ∀ h : BHist, useProcessBoundaryDecodeBHist (useProcessBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem useProcessBoundary_mk_congr
    {U U' P P' R R' E E' H H' C C' K K' N N' : BHist}
    (hU : U' = U)
    (hP : P' = P)
    (hR : R' = R)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hK : K' = K)
    (hN : N' = N) :
    UseProcessBoundaryUp.mk U' P' R' E' H' C' K' N' =
      UseProcessBoundaryUp.mk U P R E H C K N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hU
  cases hP
  cases hR
  cases hE
  cases hH
  cases hC
  cases hK
  cases hN
  rfl

def useProcessBoundaryFields : UseProcessBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UseProcessBoundaryUp.mk U P R E H C K N => [U, P, R, E, H, C, K, N]

def useProcessBoundaryToEventFlow : UseProcessBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UseProcessBoundaryUp.mk U P R E H C K N =>
      [useProcessBoundaryEncodeBHist U,
        useProcessBoundaryEncodeBHist P,
        useProcessBoundaryEncodeBHist R,
        useProcessBoundaryEncodeBHist E,
        useProcessBoundaryEncodeBHist H,
        useProcessBoundaryEncodeBHist C,
        useProcessBoundaryEncodeBHist K,
        useProcessBoundaryEncodeBHist N]

private def useProcessBoundaryEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => useProcessBoundaryEventAtDefault index rest

def useProcessBoundaryFromEventFlow (ef : EventFlow) : Option UseProcessBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UseProcessBoundaryUp.mk
      (useProcessBoundaryDecodeBHist (useProcessBoundaryEventAtDefault 0 ef))
      (useProcessBoundaryDecodeBHist (useProcessBoundaryEventAtDefault 1 ef))
      (useProcessBoundaryDecodeBHist (useProcessBoundaryEventAtDefault 2 ef))
      (useProcessBoundaryDecodeBHist (useProcessBoundaryEventAtDefault 3 ef))
      (useProcessBoundaryDecodeBHist (useProcessBoundaryEventAtDefault 4 ef))
      (useProcessBoundaryDecodeBHist (useProcessBoundaryEventAtDefault 5 ef))
      (useProcessBoundaryDecodeBHist (useProcessBoundaryEventAtDefault 6 ef))
      (useProcessBoundaryDecodeBHist (useProcessBoundaryEventAtDefault 7 ef)))

private theorem useProcessBoundary_round_trip :
    ∀ x : UseProcessBoundaryUp,
      useProcessBoundaryFromEventFlow (useProcessBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U P R E H C K N =>
      exact
        congrArg some
          (useProcessBoundary_mk_congr
            (useProcessBoundary_decode_encode_bhist U)
            (useProcessBoundary_decode_encode_bhist P)
            (useProcessBoundary_decode_encode_bhist R)
            (useProcessBoundary_decode_encode_bhist E)
            (useProcessBoundary_decode_encode_bhist H)
            (useProcessBoundary_decode_encode_bhist C)
            (useProcessBoundary_decode_encode_bhist K)
            (useProcessBoundary_decode_encode_bhist N))

private theorem useProcessBoundaryToEventFlow_injective
    {x y : UseProcessBoundaryUp} :
    useProcessBoundaryToEventFlow x = useProcessBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      useProcessBoundaryFromEventFlow (useProcessBoundaryToEventFlow x) =
        useProcessBoundaryFromEventFlow (useProcessBoundaryToEventFlow y) :=
    congrArg useProcessBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (useProcessBoundary_round_trip x).symm
      (Eq.trans hread (useProcessBoundary_round_trip y)))

private theorem useProcessBoundary_fields_faithful :
    ∀ x y : UseProcessBoundaryUp,
      useProcessBoundaryFields x = useProcessBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U₁ P₁ R₁ E₁ H₁ C₁ K₁ N₁ =>
      cases y with
      | mk U₂ P₂ R₂ E₂ H₂ C₂ K₂ N₂ =>
          cases hfields
          rfl

instance useProcessBoundaryBHistCarrier : BHistCarrier UseProcessBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := useProcessBoundaryToEventFlow
  fromEventFlow := useProcessBoundaryFromEventFlow

instance useProcessBoundaryChapterTasteGate : ChapterTasteGate UseProcessBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change useProcessBoundaryFromEventFlow (useProcessBoundaryToEventFlow x) = some x
    exact useProcessBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (useProcessBoundaryToEventFlow_injective heq)

instance useProcessBoundaryFieldFaithful : FieldFaithful UseProcessBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := useProcessBoundaryFields
  field_faithful := useProcessBoundary_fields_faithful

instance useProcessBoundaryNontrivial : Nontrivial UseProcessBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UseProcessBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UseProcessBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate UseProcessBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  useProcessBoundaryChapterTasteGate

theorem UseProcessBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, useProcessBoundaryDecodeBHist (useProcessBoundaryEncodeBHist h) = h) ∧
      (∀ x : UseProcessBoundaryUp,
        useProcessBoundaryFromEventFlow (useProcessBoundaryToEventFlow x) = some x) ∧
        (∀ x y : UseProcessBoundaryUp,
          useProcessBoundaryToEventFlow x = useProcessBoundaryToEventFlow y → x = y) ∧
          useProcessBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact useProcessBoundary_decode_encode_bhist
  · constructor
    · exact useProcessBoundary_round_trip
    · constructor
      · intro x y heq
        exact useProcessBoundaryToEventFlow_injective heq
      · rfl

end BEDC.Derived.UseProcessBoundaryUp
