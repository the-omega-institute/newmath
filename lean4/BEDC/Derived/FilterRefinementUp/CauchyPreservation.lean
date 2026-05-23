import BEDC.Derived.FilterRefinementUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.FilterRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def FilterRefinementCarrier [AskSetup] [PackageSetup]
    (source target cofinal reverse transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory cofinal ∧
    UnaryHistory reverse ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont target cofinal source ∧
        Cont source reverse replay ∧ Cont transport replay localName ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem FilterRefinement_cauchy_preservation [AskSetup] [PackageSetup]
    {source target cofinal reverse transport replay provenance localName request sourceRead
      targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterRefinementCarrier source target cofinal reverse transport replay provenance
        localName bundle pkg →
      Cont target cofinal sourceRead →
        Cont sourceRead source targetRead →
          PkgSig bundle provenance pkg →
            SemanticNameCert
                (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row source ∨ hsame row target ∨ hsame row cofinal ∨
                    hsame row sourceRead ∨ hsame row targetRead)
                (fun row : BHist => hsame row targetRead ∧ PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory targetRead ∧
                Cont target cofinal sourceRead ∧ Cont sourceRead source targetRead ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier targetCofinalSourceRead sourceReadSourceTargetRead provenancePkg
  have _ : hsame request request := hsame_refl request
  obtain ⟨sourceUnary, targetUnary, cofinalUnary, _reverseUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, _targetCofinalSource,
    _sourceReverseReplay, _transportReplayLocalName, _carrierProvenancePkg,
    _localNamePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed targetUnary cofinalUnary targetCofinalSourceRead
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed sourceReadUnary sourceUnary sourceReadSourceTargetRead
  have targetReadSource :
      hsame targetRead source ∨ hsame targetRead target ∨ hsame targetRead cofinal ∨
        hsame targetRead sourceRead ∨ hsame targetRead targetRead :=
    Or.inr (Or.inr (Or.inr (Or.inr (hsame_refl targetRead))))
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row target ∨ hsame row cofinal ∨
              hsame row sourceRead ∨ hsame row targetRead)
          (fun row : BHist => hsame row targetRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro targetRead (And.intro (hsame_refl targetRead) targetReadUnary)
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact
          And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left)
            (unary_transport sourceRow.right sameRows)
    }
    pattern_sound := by
      intro row sourceRow
      cases sourceRow.left
      exact targetReadSource
    ledger_sound := by
      intro row sourceRow
      exact And.intro sourceRow.left provenancePkg
  }
  exact
    ⟨cert, sourceReadUnary, targetReadUnary, targetCofinalSourceRead,
      sourceReadSourceTargetRead, provenancePkg⟩

theorem FilterRefinementCauchyPreservation [AskSetup] [PackageSetup]
    {source target cofinal _reverse _transport replay provenance _localName refinedRead sourceRead
      completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory source →
      UnaryHistory target →
        UnaryHistory cofinal →
          UnaryHistory replay →
            PkgSig bundle provenance pkg →
              Cont target cofinal refinedRead →
                Cont refinedRead source sourceRead →
                  Cont sourceRead replay completionRead →
                    PkgSig bundle completionRead pkg →
                      UnaryHistory refinedRead ∧ UnaryHistory sourceRead ∧
                        UnaryHistory completionRead ∧ Cont target cofinal refinedRead ∧
                          Cont refinedRead source sourceRead ∧
                            Cont sourceRead replay completionRead ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro sourceUnary targetUnary cofinalUnary replayUnary provenancePkg targetCofinalRefined
    refinedSourceRead sourceReplayCompletion completionPkg
  have refinedUnary : UnaryHistory refinedRead :=
    unary_cont_closed targetUnary cofinalUnary targetCofinalRefined
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed refinedUnary sourceUnary refinedSourceRead
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed sourceReadUnary replayUnary sourceReplayCompletion
  exact
    ⟨refinedUnary, sourceReadUnary, completionReadUnary, targetCofinalRefined,
      refinedSourceRead, sourceReplayCompletion, provenancePkg, completionPkg⟩

end BEDC.Derived.FilterRefinementUp
