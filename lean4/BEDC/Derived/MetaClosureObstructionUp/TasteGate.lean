import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaClosureObstructionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaClosureObstructionUp : Type where
  | mk :
      (refutation schema refusal truthBranch metaLoop transport continuations provenance
        nameCert : BHist) →
      MetaClosureObstructionUp
  deriving DecidableEq

def metaClosureObstructionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaClosureObstructionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaClosureObstructionEncodeBHist h

def metaClosureObstructionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaClosureObstructionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaClosureObstructionDecodeBHist tail)

private theorem metaClosureObstruction_decode_encode_bhist :
    ∀ h : BHist, metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metaClosureObstructionToEventFlow : MetaClosureObstructionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaClosureObstructionUp.mk refutation schema refusal truthBranch metaLoop transport
      continuations provenance nameCert =>
      [[BMark.b0],
        metaClosureObstructionEncodeBHist refutation,
        [BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist schema,
        [BMark.b1, BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist truthBranch,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist metaLoop,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist continuations,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaClosureObstructionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaClosureObstructionEncodeBHist nameCert]

def metaClosureObstructionFromEventFlow : EventFlow → Option MetaClosureObstructionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | refutation :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | schema :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | truthBranch :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | metaLoop :: rest9 =>
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
                                                      | continuations :: rest13 =>
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
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MetaClosureObstructionUp.mk
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    refutation)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    schema)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    refusal)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    truthBranch)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    metaLoop)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    transport)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    continuations)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    provenance)
                                                                                  (metaClosureObstructionDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem metaClosureObstruction_mk_congr
    {refutation refutation' schema schema' refusal refusal' truthBranch truthBranch'
      metaLoop metaLoop' transport transport' continuations continuations' provenance provenance'
      nameCert nameCert' : BHist}
    (hRefutation : refutation' = refutation)
    (hSchema : schema' = schema)
    (hRefusal : refusal' = refusal)
    (hTruthBranch : truthBranch' = truthBranch)
    (hMetaLoop : metaLoop' = metaLoop)
    (hTransport : transport' = transport)
    (hContinuations : continuations' = continuations)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    MetaClosureObstructionUp.mk refutation' schema' refusal' truthBranch' metaLoop' transport'
        continuations' provenance' nameCert' =
      MetaClosureObstructionUp.mk refutation schema refusal truthBranch metaLoop transport
        continuations provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRefutation
  cases hSchema
  cases hRefusal
  cases hTruthBranch
  cases hMetaLoop
  cases hTransport
  cases hContinuations
  cases hProvenance
  cases hNameCert
  rfl

private theorem metaClosureObstruction_round_trip :
    ∀ x : MetaClosureObstructionUp,
      metaClosureObstructionFromEventFlow (metaClosureObstructionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk refutation schema refusal truthBranch metaLoop transport continuations provenance nameCert =>
      change
        some
          (MetaClosureObstructionUp.mk
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist refutation))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist schema))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist refusal))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist truthBranch))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist metaLoop))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist transport))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist continuations))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist provenance))
            (metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist nameCert))) =
          some
            (MetaClosureObstructionUp.mk refutation schema refusal truthBranch metaLoop transport
              continuations provenance nameCert)
      exact
        congrArg some
          (metaClosureObstruction_mk_congr
            (metaClosureObstruction_decode_encode_bhist refutation)
            (metaClosureObstruction_decode_encode_bhist schema)
            (metaClosureObstruction_decode_encode_bhist refusal)
            (metaClosureObstruction_decode_encode_bhist truthBranch)
            (metaClosureObstruction_decode_encode_bhist metaLoop)
            (metaClosureObstruction_decode_encode_bhist transport)
            (metaClosureObstruction_decode_encode_bhist continuations)
            (metaClosureObstruction_decode_encode_bhist provenance)
            (metaClosureObstruction_decode_encode_bhist nameCert))

private theorem metaClosureObstructionToEventFlow_injective {x y : MetaClosureObstructionUp} :
    metaClosureObstructionToEventFlow x = metaClosureObstructionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaClosureObstructionFromEventFlow (metaClosureObstructionToEventFlow x) =
        metaClosureObstructionFromEventFlow (metaClosureObstructionToEventFlow y) :=
    congrArg metaClosureObstructionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaClosureObstruction_round_trip x).symm
      (Eq.trans hread (metaClosureObstruction_round_trip y)))

instance metaClosureObstructionBHistCarrier : BHistCarrier MetaClosureObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaClosureObstructionToEventFlow
  fromEventFlow := metaClosureObstructionFromEventFlow

instance metaClosureObstructionChapterTasteGate :
    ChapterTasteGate MetaClosureObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change metaClosureObstructionFromEventFlow (metaClosureObstructionToEventFlow x) = some x
    exact metaClosureObstruction_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaClosureObstructionToEventFlow_injective heq)

instance metaClosureObstructionFieldFaithful : FieldFaithful MetaClosureObstructionUp where
  fields
    | MetaClosureObstructionUp.mk refutation schema refusal truthBranch metaLoop transport
        continuations provenance nameCert =>
        [refutation, schema, refusal, truthBranch, metaLoop, transport, continuations,
          provenance, nameCert]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y hfields
    cases x with
    | mk refutation schema refusal truthBranch metaLoop transport continuations provenance
        nameCert =>
        cases y with
        | mk refutation' schema' refusal' truthBranch' metaLoop' transport' continuations'
            provenance' nameCert' =>
            cases hfields
            rfl

instance metaClosureObstructionNontrivial : Nontrivial MetaClosureObstructionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaClosureObstructionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaClosureObstructionUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaClosureObstructionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaClosureObstructionChapterTasteGate

theorem MetaClosureObstructionTasteGate_single_carrier_alignment :
    (∀ h : BHist, metaClosureObstructionDecodeBHist (metaClosureObstructionEncodeBHist h) = h) ∧
      (∀ x : MetaClosureObstructionUp,
        metaClosureObstructionFromEventFlow (metaClosureObstructionToEventFlow x) = some x) ∧
        (∀ x y : MetaClosureObstructionUp,
          metaClosureObstructionToEventFlow x = metaClosureObstructionToEventFlow y → x = y) ∧
          metaClosureObstructionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact metaClosureObstruction_decode_encode_bhist
  · constructor
    · exact metaClosureObstruction_round_trip
    · constructor
      · intro x y heq
        exact metaClosureObstructionToEventFlow_injective heq
      · rfl

theorem MetaClosureObstructionCarrier_truth_branch_obligation [AskSetup] [PackageSetup]
    {refutation schema refusal truthBranch metaLoop transport continuations provenance nameCert
      truthRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont refutation schema refusal ->
      Cont refusal truthBranch truthRead ->
        Cont truthBranch metaLoop continuations ->
          PkgSig bundle provenance pkg ->
            PkgSig bundle nameCert pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row truthRead ∧ Cont refusal truthBranch truthRead)
                  (fun row : BHist =>
                    hsame row truthRead ∧ Cont refutation schema refusal ∧
                      Cont refusal truthBranch truthRead ∧
                        Cont truthBranch metaLoop continuations)
                  (fun row : BHist =>
                    hsame row truthRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle nameCert pkg)
                  hsame ∧
                Cont refusal truthBranch truthRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro refutationRoute truthBranchRoute continuationRoute provenancePkg nameCertPkg
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact ⟨truthRead, hsame_refl truthRead, truthBranchRoute⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro row source
        exact ⟨source.left, refutationRoute, source.right, continuationRoute⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, provenancePkg, nameCertPkg⟩
    }
  · exact truthBranchRoute

theorem MetaClosureObstructionNameCertObligations [AskSetup] [PackageSetup]
    {R S F T M H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont R S C -> Cont F T M -> PkgSig bundle P pkg -> PkgSig bundle N pkg ->
      hsame H (append C P) ->
        SemanticNameCert
          (fun row : BHist => hsame row N ∧ PkgSig bundle N pkg)
          (fun row : BHist => hsame row N ∧ Cont R S C ∧ Cont F T M)
          (fun row : BHist =>
            hsame row N ∧ hsame H (append C P) ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro contRSC contFTM pkgP pkgN sameTransport
  refine
    { core :=
        { carrier_inhabited := ?_
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · exact Exists.intro N (And.intro (hsame_refl N) pkgN)
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro row other sameRows source
    exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
  · intro _row source
    exact And.intro source.left (And.intro contRSC contFTM)
  · intro _row source
    exact And.intro source.left (And.intro sameTransport (And.intro pkgP source.right))

theorem MetaClosureObstructionPublicExport [AskSetup] [PackageSetup]
    {R S F T M H C P N publicRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont R S C -> Cont F T M -> Cont T C publicRead -> PkgSig bundle P pkg ->
      PkgSig bundle N pkg -> PkgSig bundle publicRead pkg -> hsame H (append publicRead P) ->
        SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont R S C ∧ Cont F T M ∧ Cont T C publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ hsame H (append publicRead P) ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                PkgSig bundle publicRead pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro contRSC contFTM contTCPublic pkgP pkgN pkgPublic sameExport
  refine
    { core :=
        { carrier_inhabited := ?_
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · exact Exists.intro publicRead (And.intro (hsame_refl publicRead) pkgPublic)
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro row other sameRows source
    exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
  · intro _row source
    exact And.intro source.left (And.intro contRSC (And.intro contFTM contTCPublic))
  · intro _row source
    exact
      And.intro source.left
        (And.intro sameExport (And.intro pkgP (And.intro pkgN source.right)))

theorem MetaClosureObstructionTruthBranchObligation {S F T M H P truthRead : BHist} :
    Cont S F T -> Cont T M truthRead -> hsame H (append truthRead P) ->
      SemanticNameCert
        (fun row : BHist => hsame row T ∧ Cont S F T ∧ Cont T M truthRead)
        (fun row : BHist => hsame row T ∧ Cont S F T ∧ Cont T M truthRead)
        (fun row : BHist => hsame row T ∧ hsame H (append truthRead P))
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro contSFT contTMTruth sameTransport
  refine
    { core :=
        { carrier_inhabited := ?_
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · exact Exists.intro T (And.intro (hsame_refl T) (And.intro contSFT contTMTruth))
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro row other sameRows source
    exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
  · intro _row source
    exact source
  · intro _row source
    exact And.intro source.left sameTransport

end BEDC.Derived.MetaClosureObstructionUp
