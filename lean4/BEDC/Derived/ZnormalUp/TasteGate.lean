import BEDC.Derived.ZnormalUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ZNormalUp : Type where
  | mk
      (typedEndpoint finiteFuel terminalNormality normalWord continuationRead transport
        routes provenance nameCert : BHist) : ZNormalUp
  deriving DecidableEq

def zNormalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: zNormalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: zNormalEncodeBHist h

def zNormalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (zNormalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (zNormalDecodeBHist tail)

private theorem zNormalDecode_encode_bhist :
    ∀ h : BHist, zNormalDecodeBHist (zNormalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem zNormal_mk_congr
    {typedEndpoint typedEndpoint' finiteFuel finiteFuel'
      terminalNormality terminalNormality' normalWord normalWord'
      continuationRead continuationRead' transport transport' routes routes'
      provenance provenance' nameCert nameCert' : BHist}
    (hTypedEndpoint : typedEndpoint' = typedEndpoint)
    (hFiniteFuel : finiteFuel' = finiteFuel)
    (hTerminalNormality : terminalNormality' = terminalNormality)
    (hNormalWord : normalWord' = normalWord)
    (hContinuationRead : continuationRead' = continuationRead)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    ZNormalUp.mk typedEndpoint' finiteFuel' terminalNormality' normalWord'
        continuationRead' transport' routes' provenance' nameCert' =
      ZNormalUp.mk typedEndpoint finiteFuel terminalNormality normalWord continuationRead
        transport routes provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTypedEndpoint
  cases hFiniteFuel
  cases hTerminalNormality
  cases hNormalWord
  cases hContinuationRead
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hNameCert
  rfl

def zNormalToEventFlow : ZNormalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ZNormalUp.mk typedEndpoint finiteFuel terminalNormality normalWord continuationRead
      transport routes provenance nameCert =>
      [[BMark.b0],
        zNormalEncodeBHist typedEndpoint,
        [BMark.b1, BMark.b0],
        zNormalEncodeBHist finiteFuel,
        [BMark.b1, BMark.b1, BMark.b0],
        zNormalEncodeBHist terminalNormality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zNormalEncodeBHist normalWord,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zNormalEncodeBHist continuationRead,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zNormalEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zNormalEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        zNormalEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        zNormalEncodeBHist nameCert]

def zNormalFromEventFlow : EventFlow → Option ZNormalUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: typedEndpoint :: _tag1 :: finiteFuel :: _tag2 :: terminalNormality ::
      _tag3 :: normalWord :: _tag4 :: continuationRead :: _tag5 :: transport ::
        _tag6 :: routes :: _tag7 :: provenance :: _tag8 :: nameCert :: [] =>
      some
        (ZNormalUp.mk
          (zNormalDecodeBHist typedEndpoint)
          (zNormalDecodeBHist finiteFuel)
          (zNormalDecodeBHist terminalNormality)
          (zNormalDecodeBHist normalWord)
          (zNormalDecodeBHist continuationRead)
          (zNormalDecodeBHist transport)
          (zNormalDecodeBHist routes)
          (zNormalDecodeBHist provenance)
          (zNormalDecodeBHist nameCert))
  | _ => none

private theorem zNormal_round_trip :
    ∀ x : ZNormalUp, zNormalFromEventFlow (zNormalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk typedEndpoint finiteFuel terminalNormality normalWord continuationRead transport
      routes provenance nameCert =>
      change
        some
          (ZNormalUp.mk
            (zNormalDecodeBHist (zNormalEncodeBHist typedEndpoint))
            (zNormalDecodeBHist (zNormalEncodeBHist finiteFuel))
            (zNormalDecodeBHist (zNormalEncodeBHist terminalNormality))
            (zNormalDecodeBHist (zNormalEncodeBHist normalWord))
            (zNormalDecodeBHist (zNormalEncodeBHist continuationRead))
            (zNormalDecodeBHist (zNormalEncodeBHist transport))
            (zNormalDecodeBHist (zNormalEncodeBHist routes))
            (zNormalDecodeBHist (zNormalEncodeBHist provenance))
            (zNormalDecodeBHist (zNormalEncodeBHist nameCert))) =
          some
            (ZNormalUp.mk typedEndpoint finiteFuel terminalNormality normalWord
              continuationRead transport routes provenance nameCert)
      exact
        congrArg some
          (zNormal_mk_congr
            (zNormalDecode_encode_bhist typedEndpoint)
            (zNormalDecode_encode_bhist finiteFuel)
            (zNormalDecode_encode_bhist terminalNormality)
            (zNormalDecode_encode_bhist normalWord)
            (zNormalDecode_encode_bhist continuationRead)
            (zNormalDecode_encode_bhist transport)
            (zNormalDecode_encode_bhist routes)
            (zNormalDecode_encode_bhist provenance)
            (zNormalDecode_encode_bhist nameCert))

private theorem zNormalToEventFlow_injective {x y : ZNormalUp} :
    zNormalToEventFlow x = zNormalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zNormalFromEventFlow (zNormalToEventFlow x) =
        zNormalFromEventFlow (zNormalToEventFlow y) :=
    congrArg zNormalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (zNormal_round_trip x).symm (Eq.trans hread (zNormal_round_trip y)))

instance zNormalBHistCarrier : BHistCarrier ZNormalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := zNormalToEventFlow
  fromEventFlow := zNormalFromEventFlow

instance zNormalChapterTasteGate : ChapterTasteGate ZNormalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change zNormalFromEventFlow (zNormalToEventFlow x) = some x
    exact zNormal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (zNormalToEventFlow_injective heq)

def zNormalFields : ZNormalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ZNormalUp.mk typedEndpoint finiteFuel terminalNormality normalWord continuationRead
      transport routes provenance nameCert =>
      [typedEndpoint, finiteFuel, terminalNormality, normalWord, continuationRead,
        transport, routes, provenance, nameCert]

private theorem zNormal_fields_faithful :
    ∀ x y : ZNormalUp, zNormalFields x = zNormalFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk typedEndpoint finiteFuel terminalNormality normalWord continuationRead transport
      routes provenance nameCert =>
      cases y with
      | mk typedEndpoint' finiteFuel' terminalNormality' normalWord' continuationRead'
          transport' routes' provenance' nameCert' =>
          cases hfields
          rfl

instance zNormalFieldFaithful : FieldFaithful ZNormalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := zNormalFields
  field_faithful := zNormal_fields_faithful

instance zNormalNontrivial : Nontrivial ZNormalUp where
  witness_pair :=
    ⟨ZNormalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ZNormalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem ZNormalTasteGate_single_carrier_alignment :
    (∀ h : BHist, zNormalDecodeBHist (zNormalEncodeBHist h) = h) ∧
      (∀ x y : ZNormalUp, zNormalFields x = zNormalFields y → x = y) ∧
        (∃ x y : ZNormalUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact zNormalDecode_encode_bhist
  · constructor
    · intro x y hfields
      cases x with
      | mk typedEndpoint finiteFuel terminalNormality normalWord continuationRead transport
          routes provenance nameCert =>
          cases y with
          | mk typedEndpoint' finiteFuel' terminalNormality' normalWord' continuationRead'
              transport' routes' provenance' nameCert' =>
              cases hfields
              rfl
    · exact
        Exists.intro
          (ZNormalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
          (Exists.intro
            (ZNormalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
            (by
              intro h
              cases h))

end BEDC.Derived.ZnormalUp
