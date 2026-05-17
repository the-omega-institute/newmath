import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelAuditWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelAuditWitnessUp : Type where
  | mk :
      (generator acceptance ledger ancestry transport replay provenance name : BHist) →
      KernelAuditWitnessUp
  deriving DecidableEq

private def kernelAuditWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelAuditWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelAuditWitnessEncodeBHist h

private def kernelAuditWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelAuditWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelAuditWitnessDecodeBHist tail)

private theorem kernelAuditWitnessDecode_encode_bhist :
    ∀ h : BHist, kernelAuditWitnessDecodeBHist (kernelAuditWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem kernelAuditWitness_mk_congr
    {generator generator' acceptance acceptance' ledger ledger' ancestry ancestry'
      transport transport' replay replay' provenance provenance' name name' : BHist}
    (hGenerator : generator' = generator)
    (hAcceptance : acceptance' = acceptance)
    (hLedger : ledger' = ledger)
    (hAncestry : ancestry' = ancestry)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    KernelAuditWitnessUp.mk generator' acceptance' ledger' ancestry' transport' replay'
        provenance' name' =
      KernelAuditWitnessUp.mk generator acceptance ledger ancestry transport replay provenance
        name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hGenerator
  cases hAcceptance
  cases hLedger
  cases hAncestry
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

private def kernelAuditWitnessToEventFlow : KernelAuditWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelAuditWitnessUp.mk generator acceptance ledger ancestry transport replay provenance
      name =>
      [[BMark.b0],
        kernelAuditWitnessEncodeBHist generator,
        [BMark.b1, BMark.b0],
        kernelAuditWitnessEncodeBHist acceptance,
        [BMark.b1, BMark.b1, BMark.b0],
        kernelAuditWitnessEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAuditWitnessEncodeBHist ancestry,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAuditWitnessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAuditWitnessEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAuditWitnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kernelAuditWitnessEncodeBHist name]

private def kernelAuditWitnessFromEventFlow : EventFlow → Option KernelAuditWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | generator :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | acceptance :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | ledger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | ancestry :: rest7 =>
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
                                              | replay :: rest11 =>
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
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (KernelAuditWitnessUp.mk
                                                                          (kernelAuditWitnessDecodeBHist generator)
                                                                          (kernelAuditWitnessDecodeBHist acceptance)
                                                                          (kernelAuditWitnessDecodeBHist ledger)
                                                                          (kernelAuditWitnessDecodeBHist ancestry)
                                                                          (kernelAuditWitnessDecodeBHist transport)
                                                                          (kernelAuditWitnessDecodeBHist replay)
                                                                          (kernelAuditWitnessDecodeBHist provenance)
                                                                          (kernelAuditWitnessDecodeBHist name))
                                                                  | _ :: _ => none

private theorem kernelAuditWitness_round_trip :
    ∀ x : KernelAuditWitnessUp,
      kernelAuditWitnessFromEventFlow (kernelAuditWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generator acceptance ledger ancestry transport replay provenance name =>
      change
        some
          (KernelAuditWitnessUp.mk
            (kernelAuditWitnessDecodeBHist (kernelAuditWitnessEncodeBHist generator))
            (kernelAuditWitnessDecodeBHist (kernelAuditWitnessEncodeBHist acceptance))
            (kernelAuditWitnessDecodeBHist (kernelAuditWitnessEncodeBHist ledger))
            (kernelAuditWitnessDecodeBHist (kernelAuditWitnessEncodeBHist ancestry))
            (kernelAuditWitnessDecodeBHist (kernelAuditWitnessEncodeBHist transport))
            (kernelAuditWitnessDecodeBHist (kernelAuditWitnessEncodeBHist replay))
            (kernelAuditWitnessDecodeBHist (kernelAuditWitnessEncodeBHist provenance))
            (kernelAuditWitnessDecodeBHist (kernelAuditWitnessEncodeBHist name))) =
          some
            (KernelAuditWitnessUp.mk generator acceptance ledger ancestry transport replay
              provenance name)
      exact
        congrArg some
          (kernelAuditWitness_mk_congr
            (kernelAuditWitnessDecode_encode_bhist generator)
            (kernelAuditWitnessDecode_encode_bhist acceptance)
            (kernelAuditWitnessDecode_encode_bhist ledger)
            (kernelAuditWitnessDecode_encode_bhist ancestry)
            (kernelAuditWitnessDecode_encode_bhist transport)
            (kernelAuditWitnessDecode_encode_bhist replay)
            (kernelAuditWitnessDecode_encode_bhist provenance)
            (kernelAuditWitnessDecode_encode_bhist name))

private theorem kernelAuditWitnessToEventFlow_injective {x y : KernelAuditWitnessUp} :
    kernelAuditWitnessToEventFlow x = kernelAuditWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelAuditWitnessFromEventFlow (kernelAuditWitnessToEventFlow x) =
        kernelAuditWitnessFromEventFlow (kernelAuditWitnessToEventFlow y) :=
    congrArg kernelAuditWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kernelAuditWitness_round_trip x).symm
      (Eq.trans hread (kernelAuditWitness_round_trip y)))

instance kernelAuditWitnessBHistCarrier : BHistCarrier KernelAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelAuditWitnessToEventFlow
  fromEventFlow := kernelAuditWitnessFromEventFlow

instance kernelAuditWitnessChapterTasteGate : ChapterTasteGate KernelAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kernelAuditWitnessFromEventFlow (kernelAuditWitnessToEventFlow x) = some x
    exact kernelAuditWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kernelAuditWitnessToEventFlow_injective heq)

instance kernelAuditWitnessFieldFaithful : FieldFaithful KernelAuditWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | KernelAuditWitnessUp.mk generator acceptance ledger ancestry transport replay provenance
        name =>
        [generator, acceptance, ledger, ancestry, transport, replay, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk generator₁ acceptance₁ ledger₁ ancestry₁ transport₁ replay₁ provenance₁ name₁ =>
        cases y with
        | mk generator₂ acceptance₂ ledger₂ ancestry₂ transport₂ replay₂ provenance₂ name₂ =>
            injection h with hGenerator rest₁
            injection rest₁ with hAcceptance rest₂
            injection rest₂ with hLedger rest₃
            injection rest₃ with hAncestry rest₄
            injection rest₄ with hTransport rest₅
            injection rest₅ with hReplay rest₆
            injection rest₆ with hProvenance rest₇
            injection rest₇ with hName _
            cases hGenerator
            cases hAcceptance
            cases hLedger
            cases hAncestry
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hName
            rfl

theorem KernelAuditWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, kernelAuditWitnessDecodeBHist (kernelAuditWitnessEncodeBHist h) = h) ∧
      (∀ x : KernelAuditWitnessUp,
        kernelAuditWitnessFromEventFlow (kernelAuditWitnessToEventFlow x) = some x) ∧
        (∀ x y : KernelAuditWitnessUp,
          kernelAuditWitnessToEventFlow x = kernelAuditWitnessToEventFlow y → x = y) ∧
          kernelAuditWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kernelAuditWitnessDecode_encode_bhist
  · constructor
    · exact kernelAuditWitness_round_trip
    · constructor
      · intro x y heq
        exact kernelAuditWitnessToEventFlow_injective heq
      · rfl

theorem KernelAuditWitnessNameCert_obligations {G A L R H C P N : BHist}
    (candidateRoute : Cont G A C)
    (ledgerRoute : Cont A L C)
    (ancestryRoute : Cont L R C) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row G ∧
          ∃ packet : KernelAuditWitnessUp,
            packet = KernelAuditWitnessUp.mk G A L R H C P N)
      (fun row : BHist =>
        hsame row G ∧ hsame A A ∧ hsame L L ∧ hsame R R)
      (fun row : BHist =>
        Cont G A C ∧ Cont A L C ∧ Cont L R C ∧ hsame row G ∧
          hsame P P ∧ hsame N N)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro G
          ⟨hsame_refl G,
            Exists.intro (KernelAuditWitnessUp.mk G A L R H C P N) rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, hsame_refl A, hsame_refl L, hsame_refl R⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨candidateRoute, ledgerRoute, ancestryRoute, sourceRow.left, hsame_refl P,
          hsame_refl N⟩
  }

theorem KernelAuditWitnessLedger_exactness {G A L R H C P N : BHist} :
    kernelAuditWitnessFromEventFlow
        (kernelAuditWitnessToEventFlow (KernelAuditWitnessUp.mk G A L R H C P N)) =
          some (KernelAuditWitnessUp.mk G A L R H C P N) ∧
      kernelAuditWitnessToEventFlow (KernelAuditWitnessUp.mk G A L R H C P N) =
        [[BMark.b0], kernelAuditWitnessEncodeBHist G, [BMark.b1, BMark.b0],
          kernelAuditWitnessEncodeBHist A, [BMark.b1, BMark.b1, BMark.b0],
          kernelAuditWitnessEncodeBHist L, [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelAuditWitnessEncodeBHist R,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelAuditWitnessEncodeBHist H,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
          kernelAuditWitnessEncodeBHist C,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b0],
          kernelAuditWitnessEncodeBHist P,
          [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
            BMark.b1, BMark.b0],
          kernelAuditWitnessEncodeBHist N] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kernelAuditWitness_round_trip (KernelAuditWitnessUp.mk G A L R H C P N)
  · rfl

theorem KernelAuditWitnessAncestry_non_contamination
    {G A L R H C P N G' A' L' R' H' C' P' N' : BHist}
    (hflow :
      BHistCarrier.toEventFlow (KernelAuditWitnessUp.mk G A L R H C P N) =
        BHistCarrier.toEventFlow (KernelAuditWitnessUp.mk G' A' L' R' H' C' P' N')) :
    R = R' ∧ L = L' ∧ C = C' ∧ N = N' ∧
      kernelAuditWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  change
    kernelAuditWitnessToEventFlow (KernelAuditWitnessUp.mk G A L R H C P N) =
      kernelAuditWitnessToEventFlow (KernelAuditWitnessUp.mk G' A' L' R' H' C' P' N') at hflow
  have hpacket :
      KernelAuditWitnessUp.mk G A L R H C P N =
        KernelAuditWitnessUp.mk G' A' L' R' H' C' P' N' :=
    kernelAuditWitnessToEventFlow_injective hflow
  injection hpacket with _ _ hL hR _ hC _ hN
  exact ⟨hR, hL, hC, hN, rfl⟩

end BEDC.Derived.KernelAuditWitnessUp
