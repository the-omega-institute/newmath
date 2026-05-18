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

end BEDC.Derived.ClosedObservationSystemUp
