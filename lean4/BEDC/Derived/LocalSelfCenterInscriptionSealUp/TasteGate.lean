import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocalSelfCenterInscriptionSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocalSelfCenterInscriptionSealUp : Type where
  | mk :
      (localRow inscription selfCenter apophatic verdict transport route provenance name : BHist) →
      LocalSelfCenterInscriptionSealUp
  deriving DecidableEq

def localSelfCenterInscriptionSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: localSelfCenterInscriptionSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: localSelfCenterInscriptionSealEncodeBHist h

def localSelfCenterInscriptionSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (localSelfCenterInscriptionSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (localSelfCenterInscriptionSealDecodeBHist tail)

private theorem LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      localSelfCenterInscriptionSealDecodeBHist
        (localSelfCenterInscriptionSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def localSelfCenterInscriptionSealFields :
    LocalSelfCenterInscriptionSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocalSelfCenterInscriptionSealUp.mk localRow inscription selfCenter apophatic verdict
      transport route provenance name =>
      [localRow, inscription, selfCenter, apophatic, verdict, transport, route, provenance, name]

def localSelfCenterInscriptionSealToEventFlow :
    LocalSelfCenterInscriptionSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (localSelfCenterInscriptionSealFields x).map
      localSelfCenterInscriptionSealEncodeBHist

private def localSelfCenterInscriptionSealDecodePacket
    (localRow inscription selfCenter apophatic verdict transport route provenance name :
      RawEvent) : LocalSelfCenterInscriptionSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  LocalSelfCenterInscriptionSealUp.mk
    (localSelfCenterInscriptionSealDecodeBHist localRow)
    (localSelfCenterInscriptionSealDecodeBHist inscription)
    (localSelfCenterInscriptionSealDecodeBHist selfCenter)
    (localSelfCenterInscriptionSealDecodeBHist apophatic)
    (localSelfCenterInscriptionSealDecodeBHist verdict)
    (localSelfCenterInscriptionSealDecodeBHist transport)
    (localSelfCenterInscriptionSealDecodeBHist route)
    (localSelfCenterInscriptionSealDecodeBHist provenance)
    (localSelfCenterInscriptionSealDecodeBHist name)

def localSelfCenterInscriptionSealFromEventFlow :
    EventFlow → Option LocalSelfCenterInscriptionSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | localRow :: rest0 =>
      match rest0 with
      | [] => none
      | inscription :: rest1 =>
          match rest1 with
          | [] => none
          | selfCenter :: rest2 =>
              match rest2 with
              | [] => none
              | apophatic :: rest3 =>
                  match rest3 with
                  | [] => none
                  | verdict :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | route :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (localSelfCenterInscriptionSealDecodePacket
                                              localRow inscription selfCenter apophatic verdict
                                              transport route provenance name)
                                      | _ :: _ => none

private theorem LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_round :
    ∀ x : LocalSelfCenterInscriptionSealUp,
      localSelfCenterInscriptionSealFromEventFlow
        (localSelfCenterInscriptionSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk localRow inscription selfCenter apophatic verdict transport route provenance name =>
      change
        some
          (localSelfCenterInscriptionSealDecodePacket
            (localSelfCenterInscriptionSealEncodeBHist localRow)
            (localSelfCenterInscriptionSealEncodeBHist inscription)
            (localSelfCenterInscriptionSealEncodeBHist selfCenter)
            (localSelfCenterInscriptionSealEncodeBHist apophatic)
            (localSelfCenterInscriptionSealEncodeBHist verdict)
            (localSelfCenterInscriptionSealEncodeBHist transport)
            (localSelfCenterInscriptionSealEncodeBHist route)
            (localSelfCenterInscriptionSealEncodeBHist provenance)
            (localSelfCenterInscriptionSealEncodeBHist name)) =
          some
            (LocalSelfCenterInscriptionSealUp.mk localRow inscription selfCenter apophatic
              verdict transport route provenance name)
      unfold localSelfCenterInscriptionSealDecodePacket
      rw [LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_decode localRow,
        LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_decode inscription,
        LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_decode selfCenter,
        LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_decode apophatic,
        LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_decode verdict,
        LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_decode transport,
        LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_decode route,
        LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_decode provenance,
        LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_decode name]

private theorem LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_injective
    {x y : LocalSelfCenterInscriptionSealUp} :
    localSelfCenterInscriptionSealToEventFlow x =
        localSelfCenterInscriptionSealToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      localSelfCenterInscriptionSealFromEventFlow
          (localSelfCenterInscriptionSealToEventFlow x) =
        localSelfCenterInscriptionSealFromEventFlow
          (localSelfCenterInscriptionSealToEventFlow y) :=
    congrArg localSelfCenterInscriptionSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_round x).symm
      (Eq.trans hread
        (LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_round y)))

private theorem localSelfCenterInscriptionSeal_fields_faithful :
    ∀ x y : LocalSelfCenterInscriptionSealUp,
      localSelfCenterInscriptionSealFields x = localSelfCenterInscriptionSealFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk local1 inscription1 selfCenter1 apophatic1 verdict1 transport1 route1 provenance1
      name1 =>
      cases y with
      | mk local2 inscription2 selfCenter2 apophatic2 verdict2 transport2 route2 provenance2
          name2 =>
          injection hfields with hLocal tail0
          injection tail0 with hInscription tail1
          injection tail1 with hSelfCenter tail2
          injection tail2 with hApophatic tail3
          injection tail3 with hVerdict tail4
          injection tail4 with hTransport tail5
          injection tail5 with hRoute tail6
          injection tail6 with hProvenance tail7
          injection tail7 with hName _
          cases hLocal
          cases hInscription
          cases hSelfCenter
          cases hApophatic
          cases hVerdict
          cases hTransport
          cases hRoute
          cases hProvenance
          cases hName
          rfl

instance localSelfCenterInscriptionSealBHistCarrier :
    BHistCarrier LocalSelfCenterInscriptionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := localSelfCenterInscriptionSealToEventFlow
  fromEventFlow := localSelfCenterInscriptionSealFromEventFlow

instance localSelfCenterInscriptionSealChapterTasteGate :
    ChapterTasteGate LocalSelfCenterInscriptionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      localSelfCenterInscriptionSealFromEventFlow
        (localSelfCenterInscriptionSealToEventFlow x) = some x
    exact LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_injective heq)

instance localSelfCenterInscriptionSealFieldFaithful :
    FieldFaithful LocalSelfCenterInscriptionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := localSelfCenterInscriptionSealFields
  field_faithful := localSelfCenterInscriptionSeal_fields_faithful

instance localSelfCenterInscriptionSealNontrivial :
    Nontrivial LocalSelfCenterInscriptionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocalSelfCenterInscriptionSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocalSelfCenterInscriptionSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocalSelfCenterInscriptionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      localSelfCenterInscriptionSealFromEventFlow
        (localSelfCenterInscriptionSealToEventFlow x) = some x
    exact LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_injective heq)

theorem LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        localSelfCenterInscriptionSealDecodeBHist
          (localSelfCenterInscriptionSealEncodeBHist h) = h) ∧
      (∀ x : LocalSelfCenterInscriptionSealUp,
        localSelfCenterInscriptionSealFromEventFlow
          (localSelfCenterInscriptionSealToEventFlow x) = some x) ∧
        (∀ x y : LocalSelfCenterInscriptionSealUp,
          localSelfCenterInscriptionSealToEventFlow x =
              localSelfCenterInscriptionSealToEventFlow y →
            x = y) ∧
          localSelfCenterInscriptionSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact And.intro LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_decode
    (And.intro LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_round
      (And.intro
        (by
          intro x y heq
          exact
            LocalSelfCenterInscriptionSealTasteGate_single_carrier_alignment_injective heq)
        rfl))

end BEDC.Derived.LocalSelfCenterInscriptionSealUp
