import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StandardBorelSpaceUp

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

inductive StandardBorelSpaceUp : Type where
  | mk :
      (source topology polish borel basis transport replay provenance nameCert publicRead :
        BHist) →
      StandardBorelSpaceUp
  deriving DecidableEq

private def standardBorelSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: standardBorelSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: standardBorelSpaceEncodeBHist h

private def standardBorelSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (standardBorelSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (standardBorelSpaceDecodeBHist tail)

private theorem standardBorelSpace_decode_encode_bhist :
    ∀ h : BHist, standardBorelSpaceDecodeBHist (standardBorelSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def standardBorelSpaceFields : StandardBorelSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StandardBorelSpaceUp.mk source topology polish borel basis transport replay provenance
      nameCert publicRead =>
      [source, topology, polish, borel, basis, transport, replay, provenance, nameCert,
        publicRead]

def standardBorelSpaceToEventFlow : StandardBorelSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map standardBorelSpaceEncodeBHist (standardBorelSpaceFields x)

def standardBorelSpaceFromEventFlow : EventFlow → Option StandardBorelSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | topology :: rest1 =>
          match rest1 with
          | [] => none
          | polish :: rest2 =>
              match rest2 with
              | [] => none
              | borel :: rest3 =>
                  match rest3 with
                  | [] => none
                  | basis :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | nameCert :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | publicRead :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (StandardBorelSpaceUp.mk
                                                  (standardBorelSpaceDecodeBHist source)
                                                  (standardBorelSpaceDecodeBHist topology)
                                                  (standardBorelSpaceDecodeBHist polish)
                                                  (standardBorelSpaceDecodeBHist borel)
                                                  (standardBorelSpaceDecodeBHist basis)
                                                  (standardBorelSpaceDecodeBHist transport)
                                                  (standardBorelSpaceDecodeBHist replay)
                                                  (standardBorelSpaceDecodeBHist provenance)
                                                  (standardBorelSpaceDecodeBHist nameCert)
                                                  (standardBorelSpaceDecodeBHist publicRead))
                                          | _ :: _ => none

private theorem standardBorelSpace_round_trip :
    ∀ x : StandardBorelSpaceUp,
      standardBorelSpaceFromEventFlow (standardBorelSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source topology polish borel basis transport replay provenance nameCert publicRead =>
      change
        some
          (StandardBorelSpaceUp.mk
            (standardBorelSpaceDecodeBHist (standardBorelSpaceEncodeBHist source))
            (standardBorelSpaceDecodeBHist (standardBorelSpaceEncodeBHist topology))
            (standardBorelSpaceDecodeBHist (standardBorelSpaceEncodeBHist polish))
            (standardBorelSpaceDecodeBHist (standardBorelSpaceEncodeBHist borel))
            (standardBorelSpaceDecodeBHist (standardBorelSpaceEncodeBHist basis))
            (standardBorelSpaceDecodeBHist (standardBorelSpaceEncodeBHist transport))
            (standardBorelSpaceDecodeBHist (standardBorelSpaceEncodeBHist replay))
            (standardBorelSpaceDecodeBHist (standardBorelSpaceEncodeBHist provenance))
            (standardBorelSpaceDecodeBHist (standardBorelSpaceEncodeBHist nameCert))
            (standardBorelSpaceDecodeBHist (standardBorelSpaceEncodeBHist publicRead))) =
          some
            (StandardBorelSpaceUp.mk source topology polish borel basis transport replay
              provenance nameCert publicRead)
      rw [standardBorelSpace_decode_encode_bhist source,
        standardBorelSpace_decode_encode_bhist topology,
        standardBorelSpace_decode_encode_bhist polish,
        standardBorelSpace_decode_encode_bhist borel,
        standardBorelSpace_decode_encode_bhist basis,
        standardBorelSpace_decode_encode_bhist transport,
        standardBorelSpace_decode_encode_bhist replay,
        standardBorelSpace_decode_encode_bhist provenance,
        standardBorelSpace_decode_encode_bhist nameCert,
        standardBorelSpace_decode_encode_bhist publicRead]

private theorem standardBorelSpaceToEventFlow_injective {x y : StandardBorelSpaceUp} :
    standardBorelSpaceToEventFlow x = standardBorelSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      standardBorelSpaceFromEventFlow (standardBorelSpaceToEventFlow x) =
        standardBorelSpaceFromEventFlow (standardBorelSpaceToEventFlow y) :=
    congrArg standardBorelSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (standardBorelSpace_round_trip x).symm
      (Eq.trans hread (standardBorelSpace_round_trip y)))

instance standardBorelSpaceBHistCarrier : BHistCarrier StandardBorelSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := standardBorelSpaceToEventFlow
  fromEventFlow := standardBorelSpaceFromEventFlow

instance standardBorelSpaceChapterTasteGate : ChapterTasteGate StandardBorelSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change standardBorelSpaceFromEventFlow (standardBorelSpaceToEventFlow x) = some x
    exact standardBorelSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (standardBorelSpaceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate StandardBorelSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  standardBorelSpaceChapterTasteGate

theorem StandardBorelSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source topology polish borel basis transport replay provenance nameCert publicRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory topology →
        UnaryHistory polish →
          UnaryHistory borel →
            UnaryHistory basis →
              UnaryHistory transport →
                UnaryHistory replay →
                  Cont source basis replay →
                    Cont polish borel publicRead →
                      Cont transport replay provenance →
                        PkgSig bundle provenance pkg →
                          hsame provenance nameCert →
                            SemanticNameCert
                                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row source ∨ hsame row topology ∨
                                    hsame row polish ∨ hsame row borel ∨ hsame row basis ∨
                                      hsame row publicRead ∨ hsame row replay ∨
                                        hsame row provenance ∨ hsame row nameCert)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont source basis replay ∧
                                    Cont polish borel publicRead ∧
                                      Cont transport replay provenance ∧
                                        PkgSig bundle provenance pkg)
                                hsame ∧
                              UnaryHistory publicRead ∧ UnaryHistory nameCert := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro _sourceUnary _topologyUnary polishUnary borelUnary _basisUnary transportUnary replayUnary
    sourceBasisReplay polishBorelRead transportReplayProvenance provenancePkg provenanceName
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed polishUnary borelUnary polishBorelRead
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary replayUnary transportReplayProvenance
  have nameUnary : UnaryHistory nameCert :=
    unary_transport provenanceUnary provenanceName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row topology ∨ hsame row polish ∨ hsame row borel ∨
              hsame row basis ∨ hsame row publicRead ∨ hsame row replay ∨
                hsame row provenance ∨ hsame row nameCert)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont source basis replay ∧ Cont polish borel publicRead ∧
              Cont transport replay provenance ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, sourceBasisReplay, polishBorelRead, transportReplayProvenance,
          provenancePkg⟩
  }
  exact ⟨cert, publicUnary, nameUnary⟩

end BEDC.Derived.StandardBorelSpaceUp
