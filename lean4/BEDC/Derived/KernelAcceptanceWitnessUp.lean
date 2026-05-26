import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelAcceptanceWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelAcceptanceWitnessUp : Type where
  | mk :
      (generated accepted environment axiomQuery refusal transport continuation
        provenance name : BHist) →
      KernelAcceptanceWitnessUp
  deriving DecidableEq

def kernelAcceptanceWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelAcceptanceWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelAcceptanceWitnessEncodeBHist h

def kernelAcceptanceWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelAcceptanceWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelAcceptanceWitnessDecodeBHist tail)

private theorem kernelAcceptanceWitness_decode_encode_bhist :
    ∀ h : BHist,
      kernelAcceptanceWitnessDecodeBHist (kernelAcceptanceWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def kernelAcceptanceWitnessToEventFlow : KernelAcceptanceWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelAcceptanceWitnessUp.mk generated accepted environment axiomQuery refusal
      transport continuation provenance name =>
      [[BMark.b0],
        kernelAcceptanceWitnessEncodeBHist generated,
        [BMark.b1, BMark.b0],
        kernelAcceptanceWitnessEncodeBHist accepted,
        [BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceWitnessEncodeBHist environment,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceWitnessEncodeBHist axiomQuery,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceWitnessEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceWitnessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelAcceptanceWitnessEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kernelAcceptanceWitnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        kernelAcceptanceWitnessEncodeBHist name]

def kernelAcceptanceWitnessFromEventFlow :
    EventFlow → Option KernelAcceptanceWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | generated :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | accepted :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | environment :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | axiomQuery :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | refusal :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | continuation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (KernelAcceptanceWitnessUp.mk
                                                                                  (kernelAcceptanceWitnessDecodeBHist
                                                                                    generated)
                                                                                  (kernelAcceptanceWitnessDecodeBHist
                                                                                    accepted)
                                                                                  (kernelAcceptanceWitnessDecodeBHist
                                                                                    environment)
                                                                                  (kernelAcceptanceWitnessDecodeBHist
                                                                                    axiomQuery)
                                                                                  (kernelAcceptanceWitnessDecodeBHist
                                                                                    refusal)
                                                                                  (kernelAcceptanceWitnessDecodeBHist
                                                                                    transport)
                                                                                  (kernelAcceptanceWitnessDecodeBHist
                                                                                    continuation)
                                                                                  (kernelAcceptanceWitnessDecodeBHist
                                                                                    provenance)
                                                                                  (kernelAcceptanceWitnessDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem kernelAcceptanceWitness_round_trip :
    ∀ x : KernelAcceptanceWitnessUp,
      kernelAcceptanceWitnessFromEventFlow (kernelAcceptanceWitnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generated accepted environment axiomQuery refusal transport continuation
      provenance name =>
      change
        some
          (KernelAcceptanceWitnessUp.mk
            (kernelAcceptanceWitnessDecodeBHist
              (kernelAcceptanceWitnessEncodeBHist generated))
            (kernelAcceptanceWitnessDecodeBHist
              (kernelAcceptanceWitnessEncodeBHist accepted))
            (kernelAcceptanceWitnessDecodeBHist
              (kernelAcceptanceWitnessEncodeBHist environment))
            (kernelAcceptanceWitnessDecodeBHist
              (kernelAcceptanceWitnessEncodeBHist axiomQuery))
            (kernelAcceptanceWitnessDecodeBHist
              (kernelAcceptanceWitnessEncodeBHist refusal))
            (kernelAcceptanceWitnessDecodeBHist
              (kernelAcceptanceWitnessEncodeBHist transport))
            (kernelAcceptanceWitnessDecodeBHist
              (kernelAcceptanceWitnessEncodeBHist continuation))
            (kernelAcceptanceWitnessDecodeBHist
              (kernelAcceptanceWitnessEncodeBHist provenance))
            (kernelAcceptanceWitnessDecodeBHist
              (kernelAcceptanceWitnessEncodeBHist name))) =
          some
            (KernelAcceptanceWitnessUp.mk generated accepted environment axiomQuery refusal
              transport continuation provenance name)
      rw [kernelAcceptanceWitness_decode_encode_bhist generated,
        kernelAcceptanceWitness_decode_encode_bhist accepted,
        kernelAcceptanceWitness_decode_encode_bhist environment,
        kernelAcceptanceWitness_decode_encode_bhist axiomQuery,
        kernelAcceptanceWitness_decode_encode_bhist refusal,
        kernelAcceptanceWitness_decode_encode_bhist transport,
        kernelAcceptanceWitness_decode_encode_bhist continuation,
        kernelAcceptanceWitness_decode_encode_bhist provenance,
        kernelAcceptanceWitness_decode_encode_bhist name]

private theorem kernelAcceptanceWitnessToEventFlow_injective
    {x y : KernelAcceptanceWitnessUp} :
    kernelAcceptanceWitnessToEventFlow x =
        kernelAcceptanceWitnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelAcceptanceWitnessFromEventFlow (kernelAcceptanceWitnessToEventFlow x) =
        kernelAcceptanceWitnessFromEventFlow (kernelAcceptanceWitnessToEventFlow y) :=
    congrArg kernelAcceptanceWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kernelAcceptanceWitness_round_trip x).symm
      (Eq.trans hread (kernelAcceptanceWitness_round_trip y)))

instance kernelAcceptanceWitnessBHistCarrier :
    BHistCarrier KernelAcceptanceWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelAcceptanceWitnessToEventFlow
  fromEventFlow := kernelAcceptanceWitnessFromEventFlow

instance kernelAcceptanceWitnessChapterTasteGate :
    ChapterTasteGate KernelAcceptanceWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kernelAcceptanceWitnessFromEventFlow (kernelAcceptanceWitnessToEventFlow x) =
        some x
    exact kernelAcceptanceWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kernelAcceptanceWitnessToEventFlow_injective heq)

theorem KernelAcceptanceWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kernelAcceptanceWitnessDecodeBHist (kernelAcceptanceWitnessEncodeBHist h) = h) ∧
      (∀ x : KernelAcceptanceWitnessUp,
        kernelAcceptanceWitnessFromEventFlow (kernelAcceptanceWitnessToEventFlow x) =
          some x) ∧
        (∀ x y : KernelAcceptanceWitnessUp,
          kernelAcceptanceWitnessToEventFlow x = kernelAcceptanceWitnessToEventFlow y →
            x = y) ∧
          kernelAcceptanceWitnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kernelAcceptanceWitness_decode_encode_bhist
  · constructor
    · exact kernelAcceptanceWitness_round_trip
    · constructor
      · intro x y heq
        exact kernelAcceptanceWitnessToEventFlow_injective heq
      · rfl
def KernelAcceptanceWitnessPacket [AskSetup] [PackageSetup]
    (generated accepted environmentLedger axiomQuery refusal transport routes provenance nameCert
      acceptance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory generated ∧ UnaryHistory accepted ∧ UnaryHistory environmentLedger ∧
    UnaryHistory axiomQuery ∧ UnaryHistory refusal ∧ UnaryHistory nameCert ∧
      Cont generated environmentLedger accepted ∧ Cont accepted axiomQuery transport ∧
        Cont transport refusal routes ∧ Cont routes nameCert provenance ∧
          Cont provenance accepted acceptance ∧ PkgSig bundle acceptance pkg

theorem KernelAcceptanceWitnessPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {generated accepted environmentLedger axiomQuery refusal transport routes provenance nameCert
      acceptance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelAcceptanceWitnessPacket generated accepted environmentLedger axiomQuery refusal
        transport routes provenance nameCert acceptance bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          KernelAcceptanceWitnessPacket generated accepted environmentLedger axiomQuery refusal
              transport routes provenance nameCert acceptance bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          KernelAcceptanceWitnessPacket generated accepted environmentLedger axiomQuery refusal
              transport routes provenance nameCert acceptance bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          KernelAcceptanceWitnessPacket generated accepted environmentLedger axiomQuery refusal
              transport routes provenance nameCert acceptance bundle pkg ∧ hsame row nameCert)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro packet (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem KernelAcceptanceWitnessLedgerPurity [AskSetup] [PackageSetup]
    {generated accepted environmentLedger axiomQuery refusal transport routes provenance nameCert
      acceptance purityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelAcceptanceWitnessPacket generated accepted environmentLedger axiomQuery refusal
        transport routes provenance nameCert acceptance bundle pkg →
      Cont accepted axiomQuery purityRead →
      PkgSig bundle acceptance pkg →
      UnaryHistory accepted ∧ UnaryHistory environmentLedger ∧ UnaryHistory axiomQuery ∧
        UnaryHistory refusal ∧ UnaryHistory purityRead ∧
          Cont generated environmentLedger accepted ∧ Cont accepted axiomQuery purityRead ∧
            PkgSig bundle acceptance pkg := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory PkgSig AskSetup PackageSetup
  intro packet purityCont pkgSig
  exact
    ⟨packet.right.left, packet.right.right.left, packet.right.right.right.left,
      packet.right.right.right.right.left,
      unary_cont_closed packet.right.left packet.right.right.right.left purityCont,
      packet.right.right.right.right.right.right.left, purityCont, pkgSig⟩

theorem KernelAcceptanceWitnessPublicExportPackage [AskSetup] [PackageSetup]
    {generated accepted environmentLedger axiomQuery refusal transport routes provenance nameCert
      acceptance publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelAcceptanceWitnessPacket generated accepted environmentLedger axiomQuery refusal
        transport routes provenance nameCert acceptance bundle pkg ->
      Cont acceptance refusal publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory generated ∧ UnaryHistory accepted ∧ UnaryHistory environmentLedger ∧
            UnaryHistory axiomQuery ∧ UnaryHistory refusal ∧ UnaryHistory publicRead ∧
              Cont generated environmentLedger accepted ∧ Cont accepted axiomQuery transport ∧
                Cont transport refusal routes ∧ Cont routes nameCert provenance ∧
                  Cont provenance accepted acceptance ∧ Cont acceptance refusal publicRead ∧
                    PkgSig bundle acceptance pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet publicRoute publicPkg
  obtain
    ⟨generatedUnary, acceptedUnary, environmentUnary, axiomUnary, refusalUnary,
      nameCertUnary, generatedAcceptedRoute, axiomTransportRoute, refusalRoute,
      nameCertRoute, acceptanceRoute, acceptancePkg⟩ := packet
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed acceptedUnary axiomUnary axiomTransportRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed transportUnary refusalUnary refusalRoute
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed routesUnary nameCertUnary nameCertRoute
  have acceptanceUnary : UnaryHistory acceptance :=
    unary_cont_closed provenanceUnary acceptedUnary acceptanceRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed acceptanceUnary refusalUnary publicRoute
  exact
    ⟨generatedUnary, acceptedUnary, environmentUnary, axiomUnary, refusalUnary,
      publicUnary, generatedAcceptedRoute, axiomTransportRoute, refusalRoute, nameCertRoute,
      acceptanceRoute, publicRoute, acceptancePkg, publicPkg⟩

end BEDC.Derived.KernelAcceptanceWitnessUp
