import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.Cauchy_completion_monad_lawUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionMonadLawCarrier [AskSetup] [PackageSetup]
    (monad unit idempotence bind stream dyadic regular transport replay provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory monad ∧ UnaryHistory unit ∧ UnaryHistory idempotence ∧
    UnaryHistory bind ∧ UnaryHistory stream ∧ UnaryHistory dyadic ∧
      UnaryHistory regular ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont monad unit stream ∧
          Cont idempotence bind replay ∧ Cont stream dyadic regular ∧
            Cont transport replay provenance ∧ hsame nameRow (append provenance regular) ∧
              PkgSig bundle nameRow pkg

theorem CauchyCompletionMonadLawNamecertObligations [AskSetup] [PackageSetup]
    {monad unit idempotence bind stream dyadic regular transport replay provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMonadLawCarrier monad unit idempotence bind stream dyadic regular
      transport replay provenance nameRow bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyCompletionMonadLawCarrier monad unit idempotence bind stream dyadic regular
            transport replay provenance nameRow bundle pkg ∧ hsame row nameRow)
        (fun row : BHist => hsame row nameRow ∧ UnaryHistory row)
        (fun row : BHist => PkgSig bundle nameRow pkg ∧ hsame row nameRow)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  obtain ⟨monadUnary, unitUnary, idempotenceUnary, bindUnary, streamUnary, dyadicUnary,
    regularUnary, transportUnary, replayUnary, provenanceUnary, nameUnary, monadUnitStream,
    idempotenceBindReplay, streamDyadicRegular, transportReplayProvenance, nameSame, namePkg⟩ :=
    carrier
  have sourceName :
      (fun row : BHist =>
        CauchyCompletionMonadLawCarrier monad unit idempotence bind stream dyadic regular
          transport replay provenance nameRow bundle pkg ∧ hsame row nameRow) nameRow := by
    exact
      ⟨⟨monadUnary, unitUnary, idempotenceUnary, bindUnary, streamUnary, dyadicUnary,
        regularUnary, transportUnary, replayUnary, provenanceUnary, nameUnary, monadUnitStream,
        idempotenceBindReplay, streamDyadicRegular, transportReplayProvenance, nameSame,
        namePkg⟩, hsame_refl nameRow⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro nameRow sourceName
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro row source
      exact ⟨source.right, unary_transport nameUnary (hsame_symm source.right)⟩
    ledger_sound := by
      intro _row source
      exact ⟨namePkg, source.right⟩
  }

end BEDC.Derived.Cauchy_completion_monad_lawUp
