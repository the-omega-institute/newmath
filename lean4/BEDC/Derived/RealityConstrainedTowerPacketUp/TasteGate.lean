import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedTowerPacketUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedTowerPacketUp : Type where
  | mk :
      (source schedule readback realSeal residue ledger descent transport replay provenance
        localName : BHist) →
      RealityConstrainedTowerPacketUp
  deriving DecidableEq

def realityConstrainedTowerPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedTowerPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedTowerPacketEncodeBHist h

def realityConstrainedTowerPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedTowerPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedTowerPacketDecodeBHist tail)

private theorem realityConstrainedTowerPacketDecode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedTowerPacketDecodeBHist
        (realityConstrainedTowerPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realityConstrainedTowerPacket_mk_congr
    {source source' schedule schedule' readback readback' realSeal realSeal' residue
      residue' ledger ledger' descent descent' transport transport' replay replay'
      provenance provenance' localName localName' : BHist}
    (hSource : source' = source)
    (hSchedule : schedule' = schedule)
    (hReadback : readback' = readback)
    (hRealSeal : realSeal' = realSeal)
    (hResidue : residue' = residue)
    (hLedger : ledger' = ledger)
    (hDescent : descent' = descent)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    RealityConstrainedTowerPacketUp.mk source' schedule' readback' realSeal' residue'
        ledger' descent' transport' replay' provenance' localName' =
      RealityConstrainedTowerPacketUp.mk source schedule readback realSeal residue ledger
        descent transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hSchedule
  cases hReadback
  cases hRealSeal
  cases hResidue
  cases hLedger
  cases hDescent
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def realityConstrainedTowerPacketFields :
    RealityConstrainedTowerPacketUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedTowerPacketUp.mk source schedule readback realSeal residue ledger descent
      transport replay provenance localName =>
      [source, schedule, readback, realSeal, residue, ledger, descent, transport, replay,
        provenance, localName]

def realityConstrainedTowerPacketToEventFlow :
    RealityConstrainedTowerPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (realityConstrainedTowerPacketFields x).map
        realityConstrainedTowerPacketEncodeBHist

def realityConstrainedTowerPacketFromEventFlow :
    EventFlow → Option RealityConstrainedTowerPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: [] => none
  | source :: schedule :: readback :: realSeal :: residue :: ledger :: descent ::
      transport :: replay :: provenance :: localName :: [] =>
      some
        (RealityConstrainedTowerPacketUp.mk
          (realityConstrainedTowerPacketDecodeBHist source)
          (realityConstrainedTowerPacketDecodeBHist schedule)
          (realityConstrainedTowerPacketDecodeBHist readback)
          (realityConstrainedTowerPacketDecodeBHist realSeal)
          (realityConstrainedTowerPacketDecodeBHist residue)
          (realityConstrainedTowerPacketDecodeBHist ledger)
          (realityConstrainedTowerPacketDecodeBHist descent)
          (realityConstrainedTowerPacketDecodeBHist transport)
          (realityConstrainedTowerPacketDecodeBHist replay)
          (realityConstrainedTowerPacketDecodeBHist provenance)
          (realityConstrainedTowerPacketDecodeBHist localName))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k :: _l ::
      _rest => none

private theorem realityConstrainedTowerPacket_round_trip :
    ∀ x : RealityConstrainedTowerPacketUp,
      realityConstrainedTowerPacketFromEventFlow
        (realityConstrainedTowerPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source schedule readback realSeal residue ledger descent transport replay provenance
      localName =>
      exact
        congrArg some
          (realityConstrainedTowerPacket_mk_congr
            (realityConstrainedTowerPacketDecode_encode_bhist source)
            (realityConstrainedTowerPacketDecode_encode_bhist schedule)
            (realityConstrainedTowerPacketDecode_encode_bhist readback)
            (realityConstrainedTowerPacketDecode_encode_bhist realSeal)
            (realityConstrainedTowerPacketDecode_encode_bhist residue)
            (realityConstrainedTowerPacketDecode_encode_bhist ledger)
            (realityConstrainedTowerPacketDecode_encode_bhist descent)
            (realityConstrainedTowerPacketDecode_encode_bhist transport)
            (realityConstrainedTowerPacketDecode_encode_bhist replay)
            (realityConstrainedTowerPacketDecode_encode_bhist provenance)
            (realityConstrainedTowerPacketDecode_encode_bhist localName))

private theorem realityConstrainedTowerPacketToEventFlow_injective
    {x y : RealityConstrainedTowerPacketUp} :
    realityConstrainedTowerPacketToEventFlow x =
      realityConstrainedTowerPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedTowerPacketFromEventFlow
          (realityConstrainedTowerPacketToEventFlow x) =
        realityConstrainedTowerPacketFromEventFlow
          (realityConstrainedTowerPacketToEventFlow y) :=
    congrArg realityConstrainedTowerPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedTowerPacket_round_trip x).symm
      (Eq.trans hread (realityConstrainedTowerPacket_round_trip y)))

private theorem realityConstrainedTowerPacket_field_faithful :
    ∀ x y : RealityConstrainedTowerPacketUp,
      realityConstrainedTowerPacketFields x =
        realityConstrainedTowerPacketFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source schedule readback realSeal residue ledger descent transport replay provenance
      localName =>
      cases y with
      | mk source' schedule' readback' realSeal' residue' ledger' descent' transport' replay'
          provenance' localName' =>
          cases hfields
          rfl

instance realityConstrainedTowerPacketBHistCarrier :
    BHistCarrier RealityConstrainedTowerPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedTowerPacketToEventFlow
  fromEventFlow := realityConstrainedTowerPacketFromEventFlow

instance realityConstrainedTowerPacketChapterTasteGate :
    ChapterTasteGate RealityConstrainedTowerPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedTowerPacketFromEventFlow
        (realityConstrainedTowerPacketToEventFlow x) = some x
    exact realityConstrainedTowerPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedTowerPacketToEventFlow_injective heq)

instance realityConstrainedTowerPacketFieldFaithful :
    FieldFaithful RealityConstrainedTowerPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedTowerPacketFields
  field_faithful := realityConstrainedTowerPacket_field_faithful

instance realityConstrainedTowerPacketNontrivial :
    Nontrivial RealityConstrainedTowerPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedTowerPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RealityConstrainedTowerPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedTowerPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedTowerPacketChapterTasteGate

theorem RealityConstrainedTowerPacketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedTowerPacketDecodeBHist
        (realityConstrainedTowerPacketEncodeBHist h) = h) ∧
      (∀ x : RealityConstrainedTowerPacketUp,
        realityConstrainedTowerPacketFromEventFlow
          (realityConstrainedTowerPacketToEventFlow x) = some x) ∧
        (∀ x y : RealityConstrainedTowerPacketUp,
          realityConstrainedTowerPacketToEventFlow x =
            realityConstrainedTowerPacketToEventFlow y → x = y) ∧
          realityConstrainedTowerPacketEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : RealityConstrainedTowerPacketUp,
              realityConstrainedTowerPacketFields x =
                realityConstrainedTowerPacketFields y → x = y) ∧
              (∃ x y : RealityConstrainedTowerPacketUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨realityConstrainedTowerPacketDecode_encode_bhist,
      realityConstrainedTowerPacket_round_trip,
      (fun _ _ heq => realityConstrainedTowerPacketToEventFlow_injective heq), rfl,
      realityConstrainedTowerPacket_field_faithful,
      ⟨RealityConstrainedTowerPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty,
        RealityConstrainedTowerPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

theorem RealityConstrainedTowerPacketUp_nonescape_transport
    {source schedule readback realSeal residue ledger descent transport replay provenance
      localName source2 schedule2 readback2 realSeal2 residue2 ledger2 descent2 transport2
      replay2 provenance2 localName2 : BHist} :
    realityConstrainedTowerPacketToEventFlow
        (RealityConstrainedTowerPacketUp.mk source schedule readback realSeal residue ledger
          descent transport replay provenance localName) =
      realityConstrainedTowerPacketToEventFlow
        (RealityConstrainedTowerPacketUp.mk source2 schedule2 readback2 realSeal2 residue2
          ledger2 descent2 transport2 replay2 provenance2 localName2) →
        Cont source ledger replay →
          Cont source2 ledger2 replay2 ∧ hsame source source2 ∧ hsame residue residue2 ∧
            hsame ledger ledger2 ∧ hsame descent descent2 := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro heq hCont
  have hPacket :
      RealityConstrainedTowerPacketUp.mk source schedule readback realSeal residue ledger
          descent transport replay provenance localName =
        RealityConstrainedTowerPacketUp.mk source2 schedule2 readback2 realSeal2 residue2
          ledger2 descent2 transport2 replay2 provenance2 localName2 :=
    realityConstrainedTowerPacketToEventFlow_injective heq
  cases hPacket
  exact ⟨hCont, rfl, rfl, rfl, rfl⟩

end BEDC.Derived.RealityConstrainedTowerPacketUp.TasteGate

namespace BEDC.Derived.RealityConstrainedTowerPacketUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.RealityConstrainedTowerPacketUp :=
  TasteGate.taste_gate

end BEDC.Derived.RealityConstrainedTowerPacketUp
