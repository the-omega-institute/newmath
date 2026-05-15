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
      (localHistory inscriptionPoint selfCenterRead apophaticSocket nonidentityVerdict
        transport route provenance name : BHist) →
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

private theorem localSelfCenterInscriptionSealDecode_encode_bhist :
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

private theorem localSelfCenterInscriptionSeal_mk_congr
    {localHistory localHistory' inscriptionPoint inscriptionPoint' selfCenterRead selfCenterRead'
      apophaticSocket apophaticSocket' nonidentityVerdict nonidentityVerdict'
      transport transport' route route' provenance provenance' name name' : BHist}
    (hLocalHistory : localHistory' = localHistory)
    (hInscriptionPoint : inscriptionPoint' = inscriptionPoint)
    (hSelfCenterRead : selfCenterRead' = selfCenterRead)
    (hApophaticSocket : apophaticSocket' = apophaticSocket)
    (hNonidentityVerdict : nonidentityVerdict' = nonidentityVerdict)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    LocalSelfCenterInscriptionSealUp.mk localHistory' inscriptionPoint' selfCenterRead'
        apophaticSocket' nonidentityVerdict' transport' route' provenance' name' =
      LocalSelfCenterInscriptionSealUp.mk localHistory inscriptionPoint selfCenterRead
        apophaticSocket nonidentityVerdict transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hLocalHistory
  cases hInscriptionPoint
  cases hSelfCenterRead
  cases hApophaticSocket
  cases hNonidentityVerdict
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def localSelfCenterInscriptionSealFields :
    LocalSelfCenterInscriptionSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocalSelfCenterInscriptionSealUp.mk localHistory inscriptionPoint selfCenterRead
      apophaticSocket nonidentityVerdict transport route provenance name =>
      [localHistory, inscriptionPoint, selfCenterRead, apophaticSocket, nonidentityVerdict,
        transport, route, provenance, name]

def localSelfCenterInscriptionSealToEventFlow :
    LocalSelfCenterInscriptionSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocalSelfCenterInscriptionSealUp.mk localHistory inscriptionPoint selfCenterRead
      apophaticSocket nonidentityVerdict transport route provenance name =>
      [localSelfCenterInscriptionSealEncodeBHist localHistory,
        localSelfCenterInscriptionSealEncodeBHist inscriptionPoint,
        localSelfCenterInscriptionSealEncodeBHist selfCenterRead,
        localSelfCenterInscriptionSealEncodeBHist apophaticSocket,
        localSelfCenterInscriptionSealEncodeBHist nonidentityVerdict,
        localSelfCenterInscriptionSealEncodeBHist transport,
        localSelfCenterInscriptionSealEncodeBHist route,
        localSelfCenterInscriptionSealEncodeBHist provenance,
        localSelfCenterInscriptionSealEncodeBHist name]

def localSelfCenterInscriptionSealFromEventFlow :
    EventFlow → Option LocalSelfCenterInscriptionSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | localHistory :: rest0 =>
      match rest0 with
      | [] => none
      | inscriptionPoint :: rest1 =>
          match rest1 with
          | [] => none
          | selfCenterRead :: rest2 =>
              match rest2 with
              | [] => none
              | apophaticSocket :: rest3 =>
                  match rest3 with
                  | [] => none
                  | nonidentityVerdict :: rest4 =>
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
                                            (LocalSelfCenterInscriptionSealUp.mk
                                              (localSelfCenterInscriptionSealDecodeBHist
                                                localHistory)
                                              (localSelfCenterInscriptionSealDecodeBHist
                                                inscriptionPoint)
                                              (localSelfCenterInscriptionSealDecodeBHist
                                                selfCenterRead)
                                              (localSelfCenterInscriptionSealDecodeBHist
                                                apophaticSocket)
                                              (localSelfCenterInscriptionSealDecodeBHist
                                                nonidentityVerdict)
                                              (localSelfCenterInscriptionSealDecodeBHist
                                                transport)
                                              (localSelfCenterInscriptionSealDecodeBHist route)
                                              (localSelfCenterInscriptionSealDecodeBHist
                                                provenance)
                                              (localSelfCenterInscriptionSealDecodeBHist name))
                                      | _ :: _ => none

private theorem localSelfCenterInscriptionSeal_round_trip :
    ∀ x : LocalSelfCenterInscriptionSealUp,
      localSelfCenterInscriptionSealFromEventFlow
        (localSelfCenterInscriptionSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk localHistory inscriptionPoint selfCenterRead apophaticSocket nonidentityVerdict
      transport route provenance name =>
      exact
        congrArg some
          (localSelfCenterInscriptionSeal_mk_congr
            (localSelfCenterInscriptionSealDecode_encode_bhist localHistory)
            (localSelfCenterInscriptionSealDecode_encode_bhist inscriptionPoint)
            (localSelfCenterInscriptionSealDecode_encode_bhist selfCenterRead)
            (localSelfCenterInscriptionSealDecode_encode_bhist apophaticSocket)
            (localSelfCenterInscriptionSealDecode_encode_bhist nonidentityVerdict)
            (localSelfCenterInscriptionSealDecode_encode_bhist transport)
            (localSelfCenterInscriptionSealDecode_encode_bhist route)
            (localSelfCenterInscriptionSealDecode_encode_bhist provenance)
            (localSelfCenterInscriptionSealDecode_encode_bhist name))

private theorem localSelfCenterInscriptionSealToEventFlow_injective
    {x y : LocalSelfCenterInscriptionSealUp} :
    localSelfCenterInscriptionSealToEventFlow x =
      localSelfCenterInscriptionSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      localSelfCenterInscriptionSealFromEventFlow
          (localSelfCenterInscriptionSealToEventFlow x) =
        localSelfCenterInscriptionSealFromEventFlow
          (localSelfCenterInscriptionSealToEventFlow y) :=
    congrArg localSelfCenterInscriptionSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (localSelfCenterInscriptionSeal_round_trip x).symm
      (Eq.trans hread (localSelfCenterInscriptionSeal_round_trip y)))

private theorem localSelfCenterInscriptionSeal_field_faithful :
    ∀ x y : LocalSelfCenterInscriptionSealUp,
      localSelfCenterInscriptionSealFields x =
        localSelfCenterInscriptionSealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk localHistory inscriptionPoint selfCenterRead apophaticSocket nonidentityVerdict
      transport route provenance name =>
      cases y with
      | mk localHistory' inscriptionPoint' selfCenterRead' apophaticSocket'
          nonidentityVerdict' transport' route' provenance' name' =>
          cases hfields
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
    exact localSelfCenterInscriptionSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (localSelfCenterInscriptionSealToEventFlow_injective heq)

instance localSelfCenterInscriptionSealFieldFaithful :
    FieldFaithful LocalSelfCenterInscriptionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := localSelfCenterInscriptionSealFields
  field_faithful := localSelfCenterInscriptionSeal_field_faithful

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

def taste_gate : ChapterTasteGate LocalSelfCenterInscriptionSealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  localSelfCenterInscriptionSealChapterTasteGate

theorem LocalSelfCenterInscriptionSealUp_taste_gate_boundary :
    (∀ x : LocalSelfCenterInscriptionSealUp,
      ∃ e : EventFlow, localSelfCenterInscriptionSealFromEventFlow e = some x) ∧
      (∀ (x : LocalSelfCenterInscriptionSealUp) (w : RawEvent) (m : BMark),
        List.Mem w (localSelfCenterInscriptionSealToEventFlow x) →
          List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    exact
      ⟨localSelfCenterInscriptionSealToEventFlow x,
        localSelfCenterInscriptionSeal_round_trip x⟩
  · intro x w m hw hm
    exact event_flow_conservativity (S := localSelfCenterInscriptionSealToEventFlow x) hw hm

end BEDC.Derived.LocalSelfCenterInscriptionSealUp
