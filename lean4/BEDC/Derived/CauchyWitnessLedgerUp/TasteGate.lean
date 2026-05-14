import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyWitnessLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyWitnessLedgerUp : Type where
  | mk
      (diagonalBudget observationBudget sealSynchronizer completionSealClassifier
        transport continuation provenance nameCert : BHist) :
      CauchyWitnessLedgerUp
  deriving DecidableEq

private def cauchyWitnessLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyWitnessLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyWitnessLedgerEncodeBHist h

private def cauchyWitnessLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyWitnessLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyWitnessLedgerDecodeBHist tail)

private theorem cauchyWitnessLedgerDecode_encode_bhist :
    ∀ h : BHist,
      cauchyWitnessLedgerDecodeBHist
        (cauchyWitnessLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cauchyWitnessLedger_mk_congr
    {diagonalBudget diagonalBudget' observationBudget observationBudget'
      sealSynchronizer sealSynchronizer' completionSealClassifier completionSealClassifier'
      transport transport' continuation continuation' provenance provenance'
      nameCert nameCert' : BHist}
    (hDiagonalBudget : diagonalBudget' = diagonalBudget)
    (hObservationBudget : observationBudget' = observationBudget)
    (hSealSynchronizer : sealSynchronizer' = sealSynchronizer)
    (hCompletionSealClassifier : completionSealClassifier' = completionSealClassifier)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    CauchyWitnessLedgerUp.mk diagonalBudget' observationBudget' sealSynchronizer'
        completionSealClassifier' transport' continuation' provenance' nameCert' =
      CauchyWitnessLedgerUp.mk diagonalBudget observationBudget sealSynchronizer
        completionSealClassifier transport continuation provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hDiagonalBudget
  cases hObservationBudget
  cases hSealSynchronizer
  cases hCompletionSealClassifier
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hNameCert
  rfl

private def cauchyWitnessLedgerToEventFlow :
    CauchyWitnessLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyWitnessLedgerUp.mk diagonalBudget observationBudget sealSynchronizer
      completionSealClassifier transport continuation provenance nameCert =>
      [[BMark.b0],
        cauchyWitnessLedgerEncodeBHist diagonalBudget,
        [BMark.b1, BMark.b0],
        cauchyWitnessLedgerEncodeBHist observationBudget,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessLedgerEncodeBHist sealSynchronizer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessLedgerEncodeBHist completionSealClassifier,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessLedgerEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyWitnessLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyWitnessLedgerEncodeBHist nameCert]

private def cauchyWitnessLedgerFromEventFlow :
    EventFlow → Option CauchyWitnessLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | diagonalBudget :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | observationBudget :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | sealSynchronizer :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | completionSealClassifier :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuation :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (CauchyWitnessLedgerUp.mk
                                                                          (cauchyWitnessLedgerDecodeBHist diagonalBudget)
                                                                          (cauchyWitnessLedgerDecodeBHist observationBudget)
                                                                          (cauchyWitnessLedgerDecodeBHist sealSynchronizer)
                                                                          (cauchyWitnessLedgerDecodeBHist completionSealClassifier)
                                                                          (cauchyWitnessLedgerDecodeBHist transport)
                                                                          (cauchyWitnessLedgerDecodeBHist continuation)
                                                                          (cauchyWitnessLedgerDecodeBHist provenance)
                                                                          (cauchyWitnessLedgerDecodeBHist nameCert))
                                                                  | _ :: _ => none

private theorem cauchyWitnessLedger_round_trip :
    ∀ x : CauchyWitnessLedgerUp,
      cauchyWitnessLedgerFromEventFlow
        (cauchyWitnessLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk diagonalBudget observationBudget sealSynchronizer completionSealClassifier
      transport continuation provenance nameCert =>
      change
        some
          (CauchyWitnessLedgerUp.mk
            (cauchyWitnessLedgerDecodeBHist
              (cauchyWitnessLedgerEncodeBHist diagonalBudget))
            (cauchyWitnessLedgerDecodeBHist
              (cauchyWitnessLedgerEncodeBHist observationBudget))
            (cauchyWitnessLedgerDecodeBHist
              (cauchyWitnessLedgerEncodeBHist sealSynchronizer))
            (cauchyWitnessLedgerDecodeBHist
              (cauchyWitnessLedgerEncodeBHist completionSealClassifier))
            (cauchyWitnessLedgerDecodeBHist
              (cauchyWitnessLedgerEncodeBHist transport))
            (cauchyWitnessLedgerDecodeBHist
              (cauchyWitnessLedgerEncodeBHist continuation))
            (cauchyWitnessLedgerDecodeBHist
              (cauchyWitnessLedgerEncodeBHist provenance))
            (cauchyWitnessLedgerDecodeBHist
              (cauchyWitnessLedgerEncodeBHist nameCert))) =
          some
            (CauchyWitnessLedgerUp.mk diagonalBudget observationBudget
              sealSynchronizer completionSealClassifier transport continuation
              provenance nameCert)
      exact
        congrArg some
          (cauchyWitnessLedger_mk_congr
            (cauchyWitnessLedgerDecode_encode_bhist diagonalBudget)
            (cauchyWitnessLedgerDecode_encode_bhist observationBudget)
            (cauchyWitnessLedgerDecode_encode_bhist sealSynchronizer)
            (cauchyWitnessLedgerDecode_encode_bhist completionSealClassifier)
            (cauchyWitnessLedgerDecode_encode_bhist transport)
            (cauchyWitnessLedgerDecode_encode_bhist continuation)
            (cauchyWitnessLedgerDecode_encode_bhist provenance)
            (cauchyWitnessLedgerDecode_encode_bhist nameCert))

private theorem cauchyWitnessLedgerToEventFlow_injective
    {x y : CauchyWitnessLedgerUp} :
    cauchyWitnessLedgerToEventFlow x =
      cauchyWitnessLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyWitnessLedgerFromEventFlow
          (cauchyWitnessLedgerToEventFlow x) =
        cauchyWitnessLedgerFromEventFlow
          (cauchyWitnessLedgerToEventFlow y) :=
    congrArg cauchyWitnessLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyWitnessLedger_round_trip x).symm
      (Eq.trans hread (cauchyWitnessLedger_round_trip y)))

instance cauchyWitnessLedgerBHistCarrier :
    BHistCarrier CauchyWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyWitnessLedgerToEventFlow
  fromEventFlow := cauchyWitnessLedgerFromEventFlow

instance cauchyWitnessLedgerChapterTasteGate :
    ChapterTasteGate CauchyWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyWitnessLedgerFromEventFlow
        (cauchyWitnessLedgerToEventFlow x) = some x
    exact cauchyWitnessLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyWitnessLedgerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyWitnessLedgerUp :=
  cauchyWitnessLedgerChapterTasteGate

instance cauchyWitnessLedgerFieldFaithful :
    FieldFaithful CauchyWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CauchyWitnessLedgerUp.mk diagonalBudget observationBudget sealSynchronizer
        completionSealClassifier transport continuation provenance nameCert =>
        [diagonalBudget, observationBudget, sealSynchronizer, completionSealClassifier,
          transport, continuation, provenance, nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk diagonalBudget observationBudget sealSynchronizer completionSealClassifier
        transport continuation provenance nameCert =>
        cases y with
        | mk diagonalBudget' observationBudget' sealSynchronizer'
            completionSealClassifier' transport' continuation' provenance' nameCert' =>
            cases hfields
            rfl

instance cauchyWitnessLedgerNontrivial :
    Nontrivial CauchyWitnessLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyWitnessLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyWitnessLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CauchyWitnessLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyWitnessLedgerDecodeBHist
        (cauchyWitnessLedgerEncodeBHist h) = h) ∧
      (∀ x : CauchyWitnessLedgerUp,
        cauchyWitnessLedgerFromEventFlow
          (cauchyWitnessLedgerToEventFlow x) = some x) ∧
        (∀ x y : CauchyWitnessLedgerUp,
          cauchyWitnessLedgerToEventFlow x =
            cauchyWitnessLedgerToEventFlow y → x = y) ∧
          cauchyWitnessLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cauchyWitnessLedgerDecode_encode_bhist
  · constructor
    · exact cauchyWitnessLedger_round_trip
    · constructor
      · intro x y heq
        exact cauchyWitnessLedgerToEventFlow_injective heq
      · rfl

theorem CauchyWitnessLedgerCarrier_root_namecert_threshold [AskSetup] [PackageSetup]
    {Q B S K H C P N endpoint : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont Q B S →
      Cont S K endpoint →
        hsame N endpoint →
          PkgSig bundle endpoint pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row endpoint ∧
                  ∃ packet : CauchyWitnessLedgerUp,
                    packet = CauchyWitnessLedgerUp.mk Q B S K H C P N)
              (fun row : BHist => Cont Q B S ∧ Cont S K endpoint ∧ hsame row endpoint)
              (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro routeS routeEndpoint sameName endpointPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint
          ⟨hsame_refl endpoint,
            Exists.intro (CauchyWitnessLedgerUp.mk Q B S K H C P N) rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨routeS, routeEndpoint, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, endpointPkg⟩
  }

end BEDC.Derived.CauchyWitnessLedgerUp
