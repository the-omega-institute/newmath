import BEDC.Derived.ExternalSupplyAuditRouteUp.TasteGate
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApophaticFarEndSocketUp.TasteGate

open BEDC.Derived.ExternalSupplyAuditRouteUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApophaticFarEndSocketUp : Type where
  | mk :
      (socket name farEnd gap inscription observer ledger transport route provenance
        localName : BHist) → ApophaticFarEndSocketUp
  deriving DecidableEq

def apophaticFarEndSocketEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apophaticFarEndSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apophaticFarEndSocketEncodeBHist h

def apophaticFarEndSocketDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apophaticFarEndSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apophaticFarEndSocketDecodeBHist tail)

private theorem apophaticFarEndSocketDecodeEncodeBHist :
    ∀ h : BHist,
      apophaticFarEndSocketDecodeBHist
        (apophaticFarEndSocketEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def apophaticFarEndSocketFields :
    ApophaticFarEndSocketUp → List BHist
  | ApophaticFarEndSocketUp.mk socket name farEnd gap inscription observer ledger
      transport route provenance localName =>
      [socket, name, farEnd, gap, inscription, observer, ledger, transport, route,
        provenance, localName]

def apophaticFarEndSocketToEventFlow :
    ApophaticFarEndSocketUp → EventFlow
  | x => (apophaticFarEndSocketFields x).map apophaticFarEndSocketEncodeBHist

def apophaticFarEndSocketFromEventFlow :
    EventFlow → Option ApophaticFarEndSocketUp
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
  | socket :: name :: farEnd :: gap :: inscription :: observer :: ledger :: transport ::
      route :: provenance :: localName :: [] =>
      some
        (ApophaticFarEndSocketUp.mk
          (apophaticFarEndSocketDecodeBHist socket)
          (apophaticFarEndSocketDecodeBHist name)
          (apophaticFarEndSocketDecodeBHist farEnd)
          (apophaticFarEndSocketDecodeBHist gap)
          (apophaticFarEndSocketDecodeBHist inscription)
          (apophaticFarEndSocketDecodeBHist observer)
          (apophaticFarEndSocketDecodeBHist ledger)
          (apophaticFarEndSocketDecodeBHist transport)
          (apophaticFarEndSocketDecodeBHist route)
          (apophaticFarEndSocketDecodeBHist provenance)
          (apophaticFarEndSocketDecodeBHist localName))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k :: _l ::
      _rest => none

private theorem apophaticFarEndSocketRoundTrip :
    ∀ x : ApophaticFarEndSocketUp,
      apophaticFarEndSocketFromEventFlow
        (apophaticFarEndSocketToEventFlow x) = some x := by
  intro x
  cases x with
  | mk socket name farEnd gap inscription observer ledger transport route provenance
      localName =>
      change
        some
          (ApophaticFarEndSocketUp.mk
            (apophaticFarEndSocketDecodeBHist
              (apophaticFarEndSocketEncodeBHist socket))
            (apophaticFarEndSocketDecodeBHist
              (apophaticFarEndSocketEncodeBHist name))
            (apophaticFarEndSocketDecodeBHist
              (apophaticFarEndSocketEncodeBHist farEnd))
            (apophaticFarEndSocketDecodeBHist
              (apophaticFarEndSocketEncodeBHist gap))
            (apophaticFarEndSocketDecodeBHist
              (apophaticFarEndSocketEncodeBHist inscription))
            (apophaticFarEndSocketDecodeBHist
              (apophaticFarEndSocketEncodeBHist observer))
            (apophaticFarEndSocketDecodeBHist
              (apophaticFarEndSocketEncodeBHist ledger))
            (apophaticFarEndSocketDecodeBHist
              (apophaticFarEndSocketEncodeBHist transport))
            (apophaticFarEndSocketDecodeBHist
              (apophaticFarEndSocketEncodeBHist route))
            (apophaticFarEndSocketDecodeBHist
              (apophaticFarEndSocketEncodeBHist provenance))
            (apophaticFarEndSocketDecodeBHist
              (apophaticFarEndSocketEncodeBHist localName))) =
          some
            (ApophaticFarEndSocketUp.mk socket name farEnd gap inscription observer ledger
              transport route provenance localName)
      rw [apophaticFarEndSocketDecodeEncodeBHist socket,
        apophaticFarEndSocketDecodeEncodeBHist name,
        apophaticFarEndSocketDecodeEncodeBHist farEnd,
        apophaticFarEndSocketDecodeEncodeBHist gap,
        apophaticFarEndSocketDecodeEncodeBHist inscription,
        apophaticFarEndSocketDecodeEncodeBHist observer,
        apophaticFarEndSocketDecodeEncodeBHist ledger,
        apophaticFarEndSocketDecodeEncodeBHist transport,
        apophaticFarEndSocketDecodeEncodeBHist route,
        apophaticFarEndSocketDecodeEncodeBHist provenance,
        apophaticFarEndSocketDecodeEncodeBHist localName]

private theorem apophaticFarEndSocketToEventFlowInjective
    {x y : ApophaticFarEndSocketUp} :
    apophaticFarEndSocketToEventFlow x =
      apophaticFarEndSocketToEventFlow y → x = y := by
  intro heq
  have hread :
      apophaticFarEndSocketFromEventFlow
          (apophaticFarEndSocketToEventFlow x) =
        apophaticFarEndSocketFromEventFlow
          (apophaticFarEndSocketToEventFlow y) :=
    congrArg apophaticFarEndSocketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (apophaticFarEndSocketRoundTrip x).symm
      (Eq.trans hread (apophaticFarEndSocketRoundTrip y)))

private theorem apophaticFarEndSocketFieldsFaithful :
    ∀ x y : ApophaticFarEndSocketUp,
      apophaticFarEndSocketFields x = apophaticFarEndSocketFields y → x = y := by
  intro x y hfields
  cases x with
  | mk socket name farEnd gap inscription observer ledger transport route provenance
      localName =>
      cases y with
      | mk socket' name' farEnd' gap' inscription' observer' ledger' transport' route'
          provenance' localName' =>
          cases hfields
          rfl

instance apophaticFarEndSocketBHistCarrier :
    BHistCarrier ApophaticFarEndSocketUp where
  toEventFlow := apophaticFarEndSocketToEventFlow
  fromEventFlow := apophaticFarEndSocketFromEventFlow

instance apophaticFarEndSocketChapterTasteGate :
    ChapterTasteGate ApophaticFarEndSocketUp where
  round_trip := by
    intro x
    change
      apophaticFarEndSocketFromEventFlow
        (apophaticFarEndSocketToEventFlow x) = some x
    exact apophaticFarEndSocketRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (apophaticFarEndSocketToEventFlowInjective heq)

instance apophaticFarEndSocketFieldFaithful :
    FieldFaithful ApophaticFarEndSocketUp where
  fields := apophaticFarEndSocketFields
  field_faithful := apophaticFarEndSocketFieldsFaithful

instance apophaticFarEndSocketNontrivial :
    Nontrivial ApophaticFarEndSocketUp where
  witness_pair :=
    ⟨ApophaticFarEndSocketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ApophaticFarEndSocketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ApophaticFarEndSocketUp :=
  apophaticFarEndSocketChapterTasteGate

theorem ApophaticFarEndSocketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      apophaticFarEndSocketDecodeBHist
        (apophaticFarEndSocketEncodeBHist h) = h) ∧
      (∀ x : ApophaticFarEndSocketUp,
        apophaticFarEndSocketFromEventFlow
          (apophaticFarEndSocketToEventFlow x) = some x) ∧
      (∀ x y : ApophaticFarEndSocketUp,
        apophaticFarEndSocketToEventFlow x =
          apophaticFarEndSocketToEventFlow y → x = y) ∧
      Nonempty (FieldFaithful ApophaticFarEndSocketUp) ∧
      Nonempty (Nontrivial ApophaticFarEndSocketUp) ∧
      apophaticFarEndSocketEncodeBHist BHist.Empty = ([] : List BMark) := by
  constructor
  · exact apophaticFarEndSocketDecodeEncodeBHist
  · constructor
    · exact apophaticFarEndSocketRoundTrip
    · constructor
      · intro x y heq
        exact apophaticFarEndSocketToEventFlowInjective heq
      · constructor
        · exact ⟨apophaticFarEndSocketFieldFaithful⟩
        · constructor
          · exact ⟨apophaticFarEndSocketNontrivial⟩
          · rfl

theorem ApophaticFarEndSocketNameCertObligations
    {socket name farEnd gap inscription observer ledger transport route provenance
      localName : BHist} :
    apophaticFarEndSocketFields
        (ApophaticFarEndSocketUp.mk socket name farEnd gap inscription observer ledger
          transport route provenance localName) =
      [socket, name, farEnd, gap, inscription, observer, ledger, transport, route,
        provenance, localName] ∧
      apophaticFarEndSocketDecodeBHist
        (apophaticFarEndSocketEncodeBHist localName) = localName ∧
      externalSupplyAuditRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨rfl, apophaticFarEndSocketDecodeEncodeBHist localName, rfl⟩

private def ApophaticFarEndSocketNonEscape_depth : BHist → Nat
  | BHist.Empty => 0
  | BHist.e0 h => Nat.succ (ApophaticFarEndSocketNonEscape_depth h)
  | BHist.e1 h => Nat.succ (ApophaticFarEndSocketNonEscape_depth h)

private theorem ApophaticFarEndSocketNonEscape_noSelfE0 :
    ∀ h : BHist, h ≠ BHist.e0 h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      intro hEq
      cases hEq
  | e0 tail ih =>
      intro hEq
      exact ih (BHist.e0.inj hEq)
  | e1 tail _ih =>
      intro hEq
      cases hEq

private theorem ApophaticFarEndSocketNonEscape_farEnd_eq
    {socket name farEnd farEnd' gap inscription observer ledger transport route provenance
      localName : BHist} :
    [socket, name, farEnd, gap, inscription, observer, ledger, transport, route,
        provenance, localName] =
      [socket, name, farEnd', gap, inscription, observer, ledger, transport, route,
        provenance, localName] →
      farEnd = farEnd' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  cases hfields
  rfl

theorem ApophaticFarEndSocketNonEscape
    {socket name farEnd gap inscription observer ledger transport route provenance
      localName : BHist} :
    apophaticFarEndSocketFields
        (ApophaticFarEndSocketUp.mk socket name farEnd gap inscription observer ledger
          transport route provenance localName) =
      [socket, name, farEnd, gap, inscription, observer, ledger, transport, route,
        provenance, localName] ∧
      apophaticFarEndSocketFields
          (ApophaticFarEndSocketUp.mk socket name farEnd gap inscription observer ledger
            transport route provenance localName) ≠
        apophaticFarEndSocketFields
          (ApophaticFarEndSocketUp.mk socket name (BHist.e0 farEnd) gap inscription
            observer ledger transport route provenance localName) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · intro hfields
    have farEndSame :
        farEnd = BHist.e0 farEnd :=
      ApophaticFarEndSocketNonEscape_farEnd_eq hfields
    exact ApophaticFarEndSocketNonEscape_noSelfE0 farEnd farEndSame

end BEDC.Derived.ApophaticFarEndSocketUp.TasteGate
