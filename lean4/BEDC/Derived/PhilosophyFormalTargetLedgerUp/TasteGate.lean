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
      (registryRow theoremRow gapRow traditionRow scienceRow cannotClaimRow closureRow
        skeletonRow boundaryRow transportRow continuationRow provenanceRow nameCertRow :
        BHist) →
      PhilosophyFormalTargetLedgerUp
  deriving DecidableEq

def philosophyFormalTargetLedgerFields :
    PhilosophyFormalTargetLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophyFormalTargetLedgerUp.mk registryRow theoremRow gapRow traditionRow scienceRow
      cannotClaimRow closureRow skeletonRow boundaryRow transportRow continuationRow
      provenanceRow nameCertRow =>
      [registryRow, theoremRow, gapRow, traditionRow, scienceRow, cannotClaimRow,
        closureRow, skeletonRow, boundaryRow, transportRow, continuationRow,
        provenanceRow, nameCertRow]

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
    {registryRow registryRow' theoremRow theoremRow' gapRow gapRow'
      traditionRow traditionRow' scienceRow scienceRow'
      cannotClaimRow cannotClaimRow' closureRow closureRow'
      skeletonRow skeletonRow' boundaryRow boundaryRow'
      transportRow transportRow' continuationRow continuationRow'
      provenanceRow provenanceRow' nameCertRow nameCertRow' : BHist}
    (hRegistry : registryRow' = registryRow)
    (hTheorem : theoremRow' = theoremRow)
    (hGap : gapRow' = gapRow)
    (hTradition : traditionRow' = traditionRow)
    (hScience : scienceRow' = scienceRow)
    (hCannotClaim : cannotClaimRow' = cannotClaimRow)
    (hClosure : closureRow' = closureRow)
    (hSkeleton : skeletonRow' = skeletonRow)
    (hBoundary : boundaryRow' = boundaryRow)
    (hTransport : transportRow' = transportRow)
    (hContinuation : continuationRow' = continuationRow)
    (hProvenance : provenanceRow' = provenanceRow)
    (hNameCert : nameCertRow' = nameCertRow) :
    PhilosophyFormalTargetLedgerUp.mk registryRow' theoremRow' gapRow' traditionRow'
        scienceRow' cannotClaimRow' closureRow' skeletonRow' boundaryRow' transportRow'
        continuationRow' provenanceRow' nameCertRow' =
      PhilosophyFormalTargetLedgerUp.mk registryRow theoremRow gapRow traditionRow
        scienceRow cannotClaimRow closureRow skeletonRow boundaryRow transportRow
        continuationRow provenanceRow nameCertRow := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRegistry
  cases hTheorem
  cases hGap
  cases hTradition
  cases hScience
  cases hCannotClaim
  cases hClosure
  cases hSkeleton
  cases hBoundary
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hNameCert
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
  | [] => none
  | registryRow :: rest0 =>
      match rest0 with
      | [] => none
      | theoremRow :: rest1 =>
          match rest1 with
          | [] => none
          | gapRow :: rest2 =>
              match rest2 with
              | [] => none
              | traditionRow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | scienceRow :: rest4 =>
                      match rest4 with
                      | [] => none
                      | cannotClaimRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | closureRow :: rest6 =>
                              match rest6 with
                              | [] => none
                              | skeletonRow :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | boundaryRow :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transportRow :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | continuationRow :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenanceRow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | nameCertRow :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (PhilosophyFormalTargetLedgerUp.mk
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                registryRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                theoremRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                gapRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                traditionRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                scienceRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                cannotClaimRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                closureRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                skeletonRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                boundaryRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                transportRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                continuationRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                provenanceRow)
                                                              (philosophyFormalTargetLedgerDecodeBHist
                                                                nameCertRow))
                                                      | _ :: _ => none

private theorem philosophyFormalTargetLedger_round_trip :
    ∀ x : PhilosophyFormalTargetLedgerUp,
      philosophyFormalTargetLedgerFromEventFlow
        (philosophyFormalTargetLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk registryRow theoremRow gapRow traditionRow scienceRow cannotClaimRow closureRow
      skeletonRow boundaryRow transportRow continuationRow provenanceRow nameCertRow =>
      exact
        congrArg some
          (philosophyFormalTargetLedger_mk_congr
            (philosophyFormalTargetLedgerDecodeEncodeBHist registryRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist theoremRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist gapRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist traditionRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist scienceRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist cannotClaimRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist closureRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist skeletonRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist boundaryRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist transportRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist continuationRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist provenanceRow)
            (philosophyFormalTargetLedgerDecodeEncodeBHist nameCertRow))

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
  | mk registryRow theoremRow gapRow traditionRow scienceRow cannotClaimRow closureRow
      skeletonRow boundaryRow transportRow continuationRow provenanceRow nameCertRow =>
      cases y with
      | mk registryRow' theoremRow' gapRow' traditionRow' scienceRow' cannotClaimRow'
          closureRow' skeletonRow' boundaryRow' transportRow' continuationRow'
          provenanceRow' nameCertRow' =>
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
    ⟨PhilosophyFormalTargetLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
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
