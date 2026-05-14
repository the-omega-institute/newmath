import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CookFrontierCoordinateUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CookFrontierCoordinateUp : Type where
  | mk :
      (frontier scale sample audit failure transports routes provenance nameCert : BHist) →
        CookFrontierCoordinateUp
  deriving DecidableEq

def cookFrontierCoordinateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cookFrontierCoordinateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cookFrontierCoordinateEncodeBHist h

def cookFrontierCoordinateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cookFrontierCoordinateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cookFrontierCoordinateDecodeBHist tail)

private theorem cookFrontierCoordinateDecode_encode_bhist :
    ∀ h : BHist,
      cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cookFrontierCoordinate_mk_congr
    {frontier frontier' scale scale' sample sample' audit audit' failure failure'
      transports transports' routes routes' provenance provenance' nameCert nameCert' : BHist}
    (hFrontier : frontier' = frontier)
    (hScale : scale' = scale)
    (hSample : sample' = sample)
    (hAudit : audit' = audit)
    (hFailure : failure' = failure)
    (hTransports : transports' = transports)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    CookFrontierCoordinateUp.mk frontier' scale' sample' audit' failure' transports' routes'
        provenance' nameCert' =
      CookFrontierCoordinateUp.mk frontier scale sample audit failure transports routes provenance
        nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hFrontier
  cases hScale
  cases hSample
  cases hAudit
  cases hFailure
  cases hTransports
  cases hRoutes
  cases hProvenance
  cases hNameCert
  rfl

def cookFrontierCoordinateFields : CookFrontierCoordinateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CookFrontierCoordinateUp.mk frontier scale sample audit failure transports routes provenance
      nameCert =>
      [frontier, scale, sample, audit, failure, transports, routes, provenance, nameCert]

def cookFrontierCoordinateToEventFlow : CookFrontierCoordinateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CookFrontierCoordinateUp.mk frontier scale sample audit failure transports routes provenance
      nameCert =>
      [[BMark.b0],
        cookFrontierCoordinateEncodeBHist frontier,
        [BMark.b1, BMark.b0],
        cookFrontierCoordinateEncodeBHist scale,
        [BMark.b1, BMark.b1, BMark.b0],
        cookFrontierCoordinateEncodeBHist sample,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookFrontierCoordinateEncodeBHist audit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookFrontierCoordinateEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookFrontierCoordinateEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cookFrontierCoordinateEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cookFrontierCoordinateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cookFrontierCoordinateEncodeBHist nameCert]

private def cookFrontierCoordinateEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cookFrontierCoordinateEventAtDefault index rest

def cookFrontierCoordinateFromEventFlow (ef : EventFlow) : Option CookFrontierCoordinateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CookFrontierCoordinateUp.mk
      (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEventAtDefault 1 ef))
      (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEventAtDefault 3 ef))
      (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEventAtDefault 5 ef))
      (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEventAtDefault 7 ef))
      (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEventAtDefault 9 ef))
      (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEventAtDefault 11 ef))
      (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEventAtDefault 13 ef))
      (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEventAtDefault 15 ef))
      (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEventAtDefault 17 ef)))

private theorem cookFrontierCoordinate_round_trip :
    ∀ x : CookFrontierCoordinateUp,
      cookFrontierCoordinateFromEventFlow (cookFrontierCoordinateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk frontier scale sample audit failure transports routes provenance nameCert =>
      change
        some
          (CookFrontierCoordinateUp.mk
            (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEncodeBHist frontier))
            (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEncodeBHist scale))
            (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEncodeBHist sample))
            (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEncodeBHist audit))
            (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEncodeBHist failure))
            (cookFrontierCoordinateDecodeBHist
              (cookFrontierCoordinateEncodeBHist transports))
            (cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEncodeBHist routes))
            (cookFrontierCoordinateDecodeBHist
              (cookFrontierCoordinateEncodeBHist provenance))
            (cookFrontierCoordinateDecodeBHist
              (cookFrontierCoordinateEncodeBHist nameCert))) =
          some
            (CookFrontierCoordinateUp.mk frontier scale sample audit failure transports routes
              provenance nameCert)
      exact
        congrArg some
          (cookFrontierCoordinate_mk_congr
            (cookFrontierCoordinateDecode_encode_bhist frontier)
            (cookFrontierCoordinateDecode_encode_bhist scale)
            (cookFrontierCoordinateDecode_encode_bhist sample)
            (cookFrontierCoordinateDecode_encode_bhist audit)
            (cookFrontierCoordinateDecode_encode_bhist failure)
            (cookFrontierCoordinateDecode_encode_bhist transports)
            (cookFrontierCoordinateDecode_encode_bhist routes)
            (cookFrontierCoordinateDecode_encode_bhist provenance)
            (cookFrontierCoordinateDecode_encode_bhist nameCert))

private theorem cookFrontierCoordinateToEventFlow_injective
    {x y : CookFrontierCoordinateUp} :
    cookFrontierCoordinateToEventFlow x = cookFrontierCoordinateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cookFrontierCoordinateFromEventFlow (cookFrontierCoordinateToEventFlow x) =
        cookFrontierCoordinateFromEventFlow (cookFrontierCoordinateToEventFlow y) :=
    congrArg cookFrontierCoordinateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cookFrontierCoordinate_round_trip x).symm
      (Eq.trans hread (cookFrontierCoordinate_round_trip y)))

private theorem cookFrontierCoordinate_fields_faithful :
    ∀ x y : CookFrontierCoordinateUp,
      cookFrontierCoordinateFields x = cookFrontierCoordinateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk frontier₁ scale₁ sample₁ audit₁ failure₁ transports₁ routes₁ provenance₁ nameCert₁ =>
      cases y with
      | mk frontier₂ scale₂ sample₂ audit₂ failure₂ transports₂ routes₂ provenance₂ nameCert₂ =>
          cases hfields
          rfl

instance cookFrontierCoordinateBHistCarrier :
    BHistCarrier CookFrontierCoordinateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cookFrontierCoordinateToEventFlow
  fromEventFlow := cookFrontierCoordinateFromEventFlow

instance cookFrontierCoordinateChapterTasteGate :
    ChapterTasteGate CookFrontierCoordinateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cookFrontierCoordinateFromEventFlow (cookFrontierCoordinateToEventFlow x) = some x
    exact cookFrontierCoordinate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cookFrontierCoordinateToEventFlow_injective heq)

instance cookFrontierCoordinateFieldFaithful :
    FieldFaithful CookFrontierCoordinateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cookFrontierCoordinateFields
  field_faithful := cookFrontierCoordinate_fields_faithful

instance cookFrontierCoordinateNontrivial :
    Nontrivial CookFrontierCoordinateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CookFrontierCoordinateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CookFrontierCoordinateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CookFrontierCoordinateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cookFrontierCoordinateChapterTasteGate

theorem CookFrontierCoordinateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cookFrontierCoordinateDecodeBHist (cookFrontierCoordinateEncodeBHist h) = h) ∧
      (∀ x : CookFrontierCoordinateUp,
        cookFrontierCoordinateFromEventFlow (cookFrontierCoordinateToEventFlow x) = some x) ∧
        (∀ x y : CookFrontierCoordinateUp,
          cookFrontierCoordinateToEventFlow x = cookFrontierCoordinateToEventFlow y → x = y) ∧
          cookFrontierCoordinateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cookFrontierCoordinateDecode_encode_bhist
  · constructor
    · exact cookFrontierCoordinate_round_trip
    · constructor
      · intro x y heq
        exact cookFrontierCoordinateToEventFlow_injective heq
      · rfl

end BEDC.Derived.CookFrontierCoordinateUp.TasteGate

namespace BEDC.Derived.CookFrontierCoordinateUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.CookFrontierCoordinateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.CookFrontierCoordinateUp
