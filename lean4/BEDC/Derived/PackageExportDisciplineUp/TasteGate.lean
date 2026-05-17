import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PackageExportDisciplineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PackageExportDisciplineUp : Type where
  | mk (packageMap refusalRegistry registryExport exportGate formalTarget nonSmuggling
      transport replay provenance nameCert : BHist) : PackageExportDisciplineUp
  deriving DecidableEq

def packageExportDisciplineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: packageExportDisciplineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: packageExportDisciplineEncodeBHist h

def packageExportDisciplineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (packageExportDisciplineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (packageExportDisciplineDecodeBHist tail)

theorem PackageExportDisciplineTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      packageExportDisciplineDecodeBHist (packageExportDisciplineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def packageExportDisciplineToEventFlow : PackageExportDisciplineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PackageExportDisciplineUp.mk packageMap refusalRegistry registryExport exportGate
      formalTarget nonSmuggling transport replay provenance nameCert =>
      [[BMark.b0],
        packageExportDisciplineEncodeBHist packageMap,
        [BMark.b1, BMark.b0],
        packageExportDisciplineEncodeBHist refusalRegistry,
        [BMark.b1, BMark.b1, BMark.b0],
        packageExportDisciplineEncodeBHist registryExport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packageExportDisciplineEncodeBHist exportGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packageExportDisciplineEncodeBHist formalTarget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packageExportDisciplineEncodeBHist nonSmuggling,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packageExportDisciplineEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        packageExportDisciplineEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        packageExportDisciplineEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        packageExportDisciplineEncodeBHist nameCert]

def packageExportDisciplineFromEventFlow : EventFlow → Option PackageExportDisciplineUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | packageMap :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | refusalRegistry :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | registryExport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | exportGate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | formalTarget :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | nonSmuggling :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | replay :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18
                                                                                with
                                                                              | [] => none
                                                                              | nameCert ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                    with
                                                                                  | [] =>
                                                                                      some
                                                                                        (PackageExportDisciplineUp.mk
                                                                                          (packageExportDisciplineDecodeBHist
                                                                                            packageMap)
                                                                                          (packageExportDisciplineDecodeBHist
                                                                                            refusalRegistry)
                                                                                          (packageExportDisciplineDecodeBHist
                                                                                            registryExport)
                                                                                          (packageExportDisciplineDecodeBHist
                                                                                            exportGate)
                                                                                          (packageExportDisciplineDecodeBHist
                                                                                            formalTarget)
                                                                                          (packageExportDisciplineDecodeBHist
                                                                                            nonSmuggling)
                                                                                          (packageExportDisciplineDecodeBHist
                                                                                            transport)
                                                                                          (packageExportDisciplineDecodeBHist
                                                                                            replay)
                                                                                          (packageExportDisciplineDecodeBHist
                                                                                            provenance)
                                                                                          (packageExportDisciplineDecodeBHist
                                                                                            nameCert))
                                                                                  | _ :: _ => none

theorem PackageExportDisciplineTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PackageExportDisciplineUp,
      packageExportDisciplineFromEventFlow (packageExportDisciplineToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk packageMap refusalRegistry registryExport exportGate formalTarget nonSmuggling
      transport replay provenance nameCert =>
      change
        some
          (PackageExportDisciplineUp.mk
            (packageExportDisciplineDecodeBHist
              (packageExportDisciplineEncodeBHist packageMap))
            (packageExportDisciplineDecodeBHist
              (packageExportDisciplineEncodeBHist refusalRegistry))
            (packageExportDisciplineDecodeBHist
              (packageExportDisciplineEncodeBHist registryExport))
            (packageExportDisciplineDecodeBHist
              (packageExportDisciplineEncodeBHist exportGate))
            (packageExportDisciplineDecodeBHist
              (packageExportDisciplineEncodeBHist formalTarget))
            (packageExportDisciplineDecodeBHist
              (packageExportDisciplineEncodeBHist nonSmuggling))
            (packageExportDisciplineDecodeBHist
              (packageExportDisciplineEncodeBHist transport))
            (packageExportDisciplineDecodeBHist
              (packageExportDisciplineEncodeBHist replay))
            (packageExportDisciplineDecodeBHist
              (packageExportDisciplineEncodeBHist provenance))
            (packageExportDisciplineDecodeBHist
              (packageExportDisciplineEncodeBHist nameCert))) =
          some
            (PackageExportDisciplineUp.mk packageMap refusalRegistry registryExport
              exportGate formalTarget nonSmuggling transport replay provenance nameCert)
      rw [PackageExportDisciplineTasteGate_single_carrier_alignment_decode packageMap,
        PackageExportDisciplineTasteGate_single_carrier_alignment_decode refusalRegistry,
        PackageExportDisciplineTasteGate_single_carrier_alignment_decode registryExport,
        PackageExportDisciplineTasteGate_single_carrier_alignment_decode exportGate,
        PackageExportDisciplineTasteGate_single_carrier_alignment_decode formalTarget,
        PackageExportDisciplineTasteGate_single_carrier_alignment_decode nonSmuggling,
        PackageExportDisciplineTasteGate_single_carrier_alignment_decode transport,
        PackageExportDisciplineTasteGate_single_carrier_alignment_decode replay,
        PackageExportDisciplineTasteGate_single_carrier_alignment_decode provenance,
        PackageExportDisciplineTasteGate_single_carrier_alignment_decode nameCert]

theorem PackageExportDisciplineTasteGate_single_carrier_alignment_injective
    {x y : PackageExportDisciplineUp} :
    packageExportDisciplineToEventFlow x = packageExportDisciplineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      packageExportDisciplineFromEventFlow (packageExportDisciplineToEventFlow x) =
        packageExportDisciplineFromEventFlow (packageExportDisciplineToEventFlow y) :=
    congrArg packageExportDisciplineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PackageExportDisciplineTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PackageExportDisciplineTasteGate_single_carrier_alignment_round_trip y)))

instance packageExportDisciplineBHistCarrier :
    BHistCarrier PackageExportDisciplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := packageExportDisciplineToEventFlow
  fromEventFlow := packageExportDisciplineFromEventFlow

instance packageExportDisciplineChapterTasteGate :
    ChapterTasteGate PackageExportDisciplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change packageExportDisciplineFromEventFlow (packageExportDisciplineToEventFlow x) =
      some x
    exact PackageExportDisciplineTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PackageExportDisciplineTasteGate_single_carrier_alignment_injective heq)

def packageExportDisciplineFields : PackageExportDisciplineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PackageExportDisciplineUp.mk packageMap refusalRegistry registryExport exportGate
      formalTarget nonSmuggling transport replay provenance nameCert =>
      [packageMap, refusalRegistry, registryExport, exportGate, formalTarget,
        nonSmuggling, transport, replay, provenance, nameCert]

theorem PackageExportDisciplineTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : PackageExportDisciplineUp,
      packageExportDisciplineFields x = packageExportDisciplineFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  intro x y hfields
  cases x with
  | mk packageMap1 refusalRegistry1 registryExport1 exportGate1 formalTarget1 nonSmuggling1
      transport1 replay1 provenance1 nameCert1 =>
      cases y with
      | mk packageMap2 refusalRegistry2 registryExport2 exportGate2 formalTarget2
          nonSmuggling2 transport2 replay2 provenance2 nameCert2 =>
          injection hfields with hPackageMap tail1
          cases hPackageMap
          injection tail1 with hRefusalRegistry tail2
          cases hRefusalRegistry
          injection tail2 with hRegistryExport tail3
          cases hRegistryExport
          injection tail3 with hExportGate tail4
          cases hExportGate
          injection tail4 with hFormalTarget tail5
          cases hFormalTarget
          injection tail5 with hNonSmuggling tail6
          cases hNonSmuggling
          injection tail6 with hTransport tail7
          cases hTransport
          injection tail7 with hReplay tail8
          cases hReplay
          injection tail8 with hProvenance tail9
          cases hProvenance
          injection tail9 with hNameCert _
          cases hNameCert
          rfl

instance packageExportDisciplineFieldFaithful :
    FieldFaithful PackageExportDisciplineUp where
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  fields := packageExportDisciplineFields
  field_faithful := PackageExportDisciplineTasteGate_single_carrier_alignment_field_faithful

instance packageExportDisciplineNontrivial :
    Nontrivial PackageExportDisciplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PackageExportDisciplineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PackageExportDisciplineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PackageExportDisciplineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  packageExportDisciplineChapterTasteGate

theorem PackageExportDisciplineTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        packageExportDisciplineDecodeBHist (packageExportDisciplineEncodeBHist h) = h) ∧
      packageExportDisciplineEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
        (∀ x : PackageExportDisciplineUp,
          packageExportDisciplineFromEventFlow (packageExportDisciplineToEventFlow x) =
            some x) ∧
          (∀ x y : PackageExportDisciplineUp,
            packageExportDisciplineToEventFlow x = packageExportDisciplineToEventFlow y ->
              x = y) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact PackageExportDisciplineTasteGate_single_carrier_alignment_decode
  · constructor
    · rfl
    · constructor
      · exact PackageExportDisciplineTasteGate_single_carrier_alignment_round_trip
      · intro x y heq
        exact PackageExportDisciplineTasteGate_single_carrier_alignment_injective heq

end BEDC.Derived.PackageExportDisciplineUp
