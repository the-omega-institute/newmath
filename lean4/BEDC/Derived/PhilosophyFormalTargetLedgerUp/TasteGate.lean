import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhilosophyFormalTargetLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhilosophyFormalTargetLedgerUp : Type where
  | mk :
      (registry theoremMap gapMap traditionMap scienceMap cannotClaim closureStatus
        targetSkeleton refusalBoundary transport replay provenance localName : BHist) →
      PhilosophyFormalTargetLedgerUp
  deriving DecidableEq

def philosophyFormalTargetLedgerFields :
    PhilosophyFormalTargetLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophyFormalTargetLedgerUp.mk registry theoremMap gapMap traditionMap scienceMap
      cannotClaim closureStatus targetSkeleton refusalBoundary transport replay provenance
      localName =>
      [registry, theoremMap, gapMap, traditionMap, scienceMap, cannotClaim,
        closureStatus, targetSkeleton, refusalBoundary, transport, replay, provenance,
        localName]

def philosophyFormalTargetLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: philosophyFormalTargetLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: philosophyFormalTargetLedgerEncodeBHist h

def philosophyFormalTargetLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (philosophyFormalTargetLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (philosophyFormalTargetLedgerDecodeBHist tail)

private def philosophyFormalTargetLedgerNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => philosophyFormalTargetLedgerNthRawEvent tail n

private theorem philosophyFormalTargetLedgerDecodeEncodeBHist :
    ∀ h : BHist,
      philosophyFormalTargetLedgerDecodeBHist
        (philosophyFormalTargetLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem philosophyFormalTargetLedger_mk_congr
    {registry registry' theoremMap theoremMap' gapMap gapMap'
      traditionMap traditionMap' scienceMap scienceMap' cannotClaim cannotClaim'
      closureStatus closureStatus' targetSkeleton targetSkeleton'
      refusalBoundary refusalBoundary' transport transport' replay replay'
      provenance provenance' localName localName' : BHist}
    (hRegistry : registry' = registry)
    (hTheoremMap : theoremMap' = theoremMap)
    (hGapMap : gapMap' = gapMap)
    (hTraditionMap : traditionMap' = traditionMap)
    (hScienceMap : scienceMap' = scienceMap)
    (hCannotClaim : cannotClaim' = cannotClaim)
    (hClosureStatus : closureStatus' = closureStatus)
    (hTargetSkeleton : targetSkeleton' = targetSkeleton)
    (hRefusalBoundary : refusalBoundary' = refusalBoundary)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    PhilosophyFormalTargetLedgerUp.mk registry' theoremMap' gapMap' traditionMap'
        scienceMap' cannotClaim' closureStatus' targetSkeleton' refusalBoundary'
        transport' replay' provenance' localName' =
      PhilosophyFormalTargetLedgerUp.mk registry theoremMap gapMap traditionMap
        scienceMap cannotClaim closureStatus targetSkeleton refusalBoundary transport replay
        provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRegistry
  cases hTheoremMap
  cases hGapMap
  cases hTraditionMap
  cases hScienceMap
  cases hCannotClaim
  cases hClosureStatus
  cases hTargetSkeleton
  cases hRefusalBoundary
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def philosophyFormalTargetLedgerToEventFlow :
    PhilosophyFormalTargetLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (philosophyFormalTargetLedgerFields x).map
        philosophyFormalTargetLedgerEncodeBHist

def philosophyFormalTargetLedgerFromEventFlow :
    EventFlow → Option PhilosophyFormalTargetLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (PhilosophyFormalTargetLedgerUp.mk
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 0))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 1))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 2))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 3))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 4))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 5))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 6))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 7))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 8))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 9))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 10))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 11))
          (philosophyFormalTargetLedgerDecodeBHist
            (philosophyFormalTargetLedgerNthRawEvent ef 12)))

private theorem philosophyFormalTargetLedger_round_trip :
    ∀ x : PhilosophyFormalTargetLedgerUp,
      philosophyFormalTargetLedgerFromEventFlow
        (philosophyFormalTargetLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk registry theoremMap gapMap traditionMap scienceMap cannotClaim closureStatus
      targetSkeleton refusalBoundary transport replay provenance localName =>
      exact
        congrArg some
          (philosophyFormalTargetLedger_mk_congr
            (philosophyFormalTargetLedgerDecodeEncodeBHist registry)
            (philosophyFormalTargetLedgerDecodeEncodeBHist theoremMap)
            (philosophyFormalTargetLedgerDecodeEncodeBHist gapMap)
            (philosophyFormalTargetLedgerDecodeEncodeBHist traditionMap)
            (philosophyFormalTargetLedgerDecodeEncodeBHist scienceMap)
            (philosophyFormalTargetLedgerDecodeEncodeBHist cannotClaim)
            (philosophyFormalTargetLedgerDecodeEncodeBHist closureStatus)
            (philosophyFormalTargetLedgerDecodeEncodeBHist targetSkeleton)
            (philosophyFormalTargetLedgerDecodeEncodeBHist refusalBoundary)
            (philosophyFormalTargetLedgerDecodeEncodeBHist transport)
            (philosophyFormalTargetLedgerDecodeEncodeBHist replay)
            (philosophyFormalTargetLedgerDecodeEncodeBHist provenance)
            (philosophyFormalTargetLedgerDecodeEncodeBHist localName))

private theorem philosophyFormalTargetLedgerToEventFlow_injective
    {x y : PhilosophyFormalTargetLedgerUp} :
    philosophyFormalTargetLedgerToEventFlow x =
      philosophyFormalTargetLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      philosophyFormalTargetLedgerFromEventFlow
          (philosophyFormalTargetLedgerToEventFlow x) =
        philosophyFormalTargetLedgerFromEventFlow
          (philosophyFormalTargetLedgerToEventFlow y) :=
    congrArg philosophyFormalTargetLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (philosophyFormalTargetLedger_round_trip x).symm
      (Eq.trans hread (philosophyFormalTargetLedger_round_trip y)))

private theorem philosophyFormalTargetLedger_field_faithful :
    ∀ x y : PhilosophyFormalTargetLedgerUp,
      philosophyFormalTargetLedgerFields x =
        philosophyFormalTargetLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk registry theoremMap gapMap traditionMap scienceMap cannotClaim closureStatus
      targetSkeleton refusalBoundary transport replay provenance localName =>
      cases y with
      | mk registry' theoremMap' gapMap' traditionMap' scienceMap' cannotClaim'
          closureStatus' targetSkeleton' refusalBoundary' transport' replay' provenance'
          localName' =>
          cases hfields
          rfl

instance philosophyFormalTargetLedgerBHistCarrier :
    BHistCarrier PhilosophyFormalTargetLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := philosophyFormalTargetLedgerToEventFlow
  fromEventFlow := philosophyFormalTargetLedgerFromEventFlow

instance philosophyFormalTargetLedgerChapterTasteGate :
    ChapterTasteGate PhilosophyFormalTargetLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      philosophyFormalTargetLedgerFromEventFlow
        (philosophyFormalTargetLedgerToEventFlow x) = some x
    exact philosophyFormalTargetLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (philosophyFormalTargetLedgerToEventFlow_injective heq)

instance philosophyFormalTargetLedgerFieldFaithful :
    FieldFaithful PhilosophyFormalTargetLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := philosophyFormalTargetLedgerFields
  field_faithful := philosophyFormalTargetLedger_field_faithful

instance philosophyFormalTargetLedgerNontrivial :
    Nontrivial PhilosophyFormalTargetLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhilosophyFormalTargetLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhilosophyFormalTargetLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhilosophyFormalTargetLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  philosophyFormalTargetLedgerChapterTasteGate

theorem PhilosophyFormalTargetLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      philosophyFormalTargetLedgerDecodeBHist
        (philosophyFormalTargetLedgerEncodeBHist h) = h) ∧
      philosophyFormalTargetLedgerEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (∀ x : PhilosophyFormalTargetLedgerUp,
          philosophyFormalTargetLedgerFromEventFlow
            (philosophyFormalTargetLedgerToEventFlow x) = some x) ∧
          (∀ x y : PhilosophyFormalTargetLedgerUp,
            philosophyFormalTargetLedgerToEventFlow x =
              philosophyFormalTargetLedgerToEventFlow y → x = y) ∧
            (∀ x y : PhilosophyFormalTargetLedgerUp,
              philosophyFormalTargetLedgerFields x =
                philosophyFormalTargetLedgerFields y → x = y) ∧
              (∃ x y : PhilosophyFormalTargetLedgerUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨philosophyFormalTargetLedgerDecodeEncodeBHist, rfl,
      philosophyFormalTargetLedger_round_trip,
      (fun _ _ heq => philosophyFormalTargetLedgerToEventFlow_injective heq),
      philosophyFormalTargetLedger_field_faithful,
      ⟨PhilosophyFormalTargetLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        PhilosophyFormalTargetLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.PhilosophyFormalTargetLedgerUp
