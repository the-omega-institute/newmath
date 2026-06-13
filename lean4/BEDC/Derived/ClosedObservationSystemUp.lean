import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedObservationSystemUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedObservationSystemCarrier [AskSetup] [PackageSetup]
    (observation record conservation transport continuation provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory observation ∧ UnaryHistory record ∧ UnaryHistory transport ∧
    UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
      Cont observation record conservation ∧
        hsame transport (append observation record) ∧ PkgSig bundle provenance pkg

theorem ClosedObservationSystemCarrier_gap_socket_package [AskSetup] [PackageSetup]
    {observation record conservation transport continuation provenance localName gapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedObservationSystemCarrier observation record conservation transport continuation
        provenance localName bundle pkg ->
      Cont continuation provenance gapRead ->
        PkgSig bundle gapRead pkg ->
          UnaryHistory observation ∧ UnaryHistory record ∧ UnaryHistory conservation ∧
            UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory gapRead ∧
              Cont observation record conservation ∧ Cont continuation provenance gapRead ∧
                hsame transport (append observation record) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle gapRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  intro carrier gapRoute gapPkg
  obtain ⟨observationUnary, recordUnary, _transportUnary, continuationUnary, provenanceUnary,
    _localNameUnary, observationRecordConservation, transportSame, provenancePkg⟩ := carrier
  have conservationUnary : UnaryHistory conservation :=
    unary_cont_closed observationUnary recordUnary observationRecordConservation
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed continuationUnary provenanceUnary gapRoute
  exact
    ⟨observationUnary, recordUnary, conservationUnary, continuationUnary, provenanceUnary,
      gapUnary, observationRecordConservation, gapRoute, transportSame, provenancePkg,
      gapPkg⟩

theorem ClosedObservationSystemNameCertObligations [AskSetup] [PackageSetup]
    {observation record conservation transport continuation provenance localName gapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedObservationSystemCarrier observation record conservation transport continuation
        provenance localName bundle pkg ->
      Cont continuation provenance gapRead ->
        PkgSig bundle gapRead pkg ->
          UnaryHistory observation ∧ UnaryHistory record ∧ UnaryHistory conservation ∧
            UnaryHistory gapRead ∧ Cont observation record conservation ∧
              Cont continuation provenance gapRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle gapRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  intro carrier gapRoute gapPkg
  obtain ⟨observationUnary, recordUnary, _transportUnary, continuationUnary, provenanceUnary,
    _localNameUnary, observationRecordConservation, _transportSame, provenancePkg⟩ := carrier
  have conservationUnary : UnaryHistory conservation :=
    unary_cont_closed observationUnary recordUnary observationRecordConservation
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed continuationUnary provenanceUnary gapRoute
  exact
    ⟨observationUnary, recordUnary, conservationUnary, gapUnary,
      observationRecordConservation, gapRoute, provenancePkg, gapPkg⟩

theorem ClosedObservationSystemGapSocketNonescape [AskSetup] [PackageSetup]
    {observation record conservation transport continuation provenance localName gapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedObservationSystemCarrier observation record conservation transport continuation
        provenance localName bundle pkg ->
      Cont continuation provenance gapRead ->
        PkgSig bundle gapRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                ClosedObservationSystemCarrier observation record conservation transport
                  continuation provenance localName bundle pkg ∧ hsame row localName)
              (fun row : BHist =>
                Cont observation record conservation ∧ Cont continuation provenance gapRead ∧
                  hsame row localName)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle gapRead pkg ∧
                  hsame row localName)
              hsame ∧
            UnaryHistory observation ∧ UnaryHistory record ∧ UnaryHistory conservation ∧
              UnaryHistory gapRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier gapRoute gapPkg
  have carrierWitness := carrier
  obtain ⟨observationUnary, recordUnary, _transportUnary, continuationUnary, provenanceUnary,
    _localNameUnary, observationRecordConservation, _transportSame, provenancePkg⟩ := carrier
  have conservationUnary : UnaryHistory conservation :=
    unary_cont_closed observationUnary recordUnary observationRecordConservation
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed continuationUnary provenanceUnary gapRoute
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ClosedObservationSystemCarrier observation record conservation transport continuation
            provenance localName bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          Cont observation record conservation ∧ Cont continuation provenance gapRead ∧
            hsame row localName)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle gapRead pkg ∧ hsame row localName)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro localName (And.intro carrierWitness (hsame_refl localName))
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
        intro _row _row' sameRows sourceRow
        exact And.intro sourceRow.left
          (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨observationRecordConservation, gapRoute, sourceRow.right⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨provenancePkg, gapPkg, sourceRow.right⟩
  }
  exact ⟨cert, observationUnary, recordUnary, conservationUnary, gapUnary⟩

theorem ClosedObservationSystemPrimitiveScope [AskSetup] [PackageSetup]
    {observation record conservation transport continuation provenance localName
      primitiveRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedObservationSystemCarrier observation record conservation transport continuation
        provenance localName bundle pkg →
      Cont continuation provenance primitiveRead →
        PkgSig bundle primitiveRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row localName ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row observation ∨ hsame row record ∨ hsame row conservation ∨
                  hsame row transport ∨ hsame row continuation ∨ hsame row provenance ∨
                    hsame row localName ∨ hsame row primitiveRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont observation record conservation ∧
                  Cont continuation provenance primitiveRead ∧
                    hsame transport (append observation record) ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle primitiveRead pkg)
              hsame ∧
            UnaryHistory conservation ∧ UnaryHistory primitiveRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier primitiveRoute primitivePkg
  obtain ⟨observationUnary, recordUnary, _transportUnary, continuationUnary,
    provenanceUnary, localNameUnary, observationRecordConservation, transportSame,
    provenancePkg⟩ := carrier
  have conservationUnary : UnaryHistory conservation :=
    unary_cont_closed observationUnary recordUnary observationRecordConservation
  have primitiveUnary : UnaryHistory primitiveRead :=
    unary_cont_closed continuationUnary provenanceUnary primitiveRoute
  have sourceLocal :
      (fun row : BHist => hsame row localName ∧ UnaryHistory row) localName := by
    exact ⟨hsame_refl localName, localNameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row observation ∨ hsame row record ∨ hsame row conservation ∨
              hsame row transport ∨ hsame row continuation ∨ hsame row provenance ∨
                hsame row localName ∨ hsame row primitiveRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont observation record conservation ∧
              Cont continuation provenance primitiveRead ∧
                hsame transport (append observation record) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle primitiveRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName sourceLocal
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, observationRecordConservation, primitiveRoute, transportSame,
          provenancePkg, primitivePkg⟩
  }
  exact ⟨cert, conservationUnary, primitiveUnary⟩

end BEDC.Derived.ClosedObservationSystemUp
