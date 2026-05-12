import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompletionFunctorCarrier [AskSetup] [PackageSetup]
    (monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory monad ∧ UnaryHistory universal ∧ UnaryHistory realCompletion ∧
    UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory denseMap ∧
      UnaryHistory extension ∧ UnaryHistory functorLedger ∧ UnaryHistory transport ∧
        UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont monad universal realCompletion ∧ Cont source target denseMap ∧
            Cont denseMap extension functorLedger ∧ Cont functorLedger transport routes ∧
              Cont transport routes provenance ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg

theorem CompletionFunctorCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CompletionFunctorCarrier monad universal realCompletion source target denseMap
            extension functorLedger transport routes provenance name bundle pkg ∧
            hsame row provenance)
        (fun row : BHist =>
          CompletionFunctorCarrier monad universal realCompletion source target denseMap
            extension functorLedger transport routes provenance name bundle pkg ∧
            hsame row provenance)
        (fun row : BHist =>
          CompletionFunctorCarrier monad universal realCompletion source target denseMap
            extension functorLedger transport routes provenance name bundle pkg ∧
            hsame row provenance)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro carrier (hsame_refl provenance))
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

end BEDC.Derived.CompletionFunctorUp
