import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContinuityCarrierNameCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContinuityCarrierNameCert_semantic_name_certificate [AskSetup] [PackageSetup]
    {dense sourceMap extension uniqueness window readback tolerance realSeal transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dense → UnaryHistory sourceMap → UnaryHistory extension →
      UnaryHistory uniqueness → UnaryHistory window → UnaryHistory readback →
      UnaryHistory tolerance → UnaryHistory realSeal → UnaryHistory transport →
      UnaryHistory replay → UnaryHistory provenance → UnaryHistory localName →
      Cont dense window readback → Cont readback tolerance sourceMap →
      Cont sourceMap extension realSeal → hsame transport (append replay provenance) →
      PkgSig bundle provenance pkg →
      SemanticNameCert
        (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row dense ∨ hsame row sourceMap ∨ hsame row extension ∨ hsame row realSeal)
        (fun row : BHist => hsame row realSeal ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont Pkg SemanticNameCert hsame UnaryHistory
  intro denseUnary sourceMapUnary extensionUnary _uniquenessUnary windowUnary readbackUnary
    toleranceUnary _realSealUnary _transportUnary _replayUnary _provenanceUnary _localNameUnary
    denseWindow readbackTolerance sourceExtension _transportReplay provenancePkg
  have readbackClosed : UnaryHistory readback :=
    unary_cont_closed denseUnary windowUnary denseWindow
  have sourceMapClosed : UnaryHistory sourceMap :=
    unary_cont_closed readbackUnary toleranceUnary readbackTolerance
  have realSealClosed : UnaryHistory realSeal :=
    unary_cont_closed sourceMapUnary extensionUnary sourceExtension
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro realSeal (And.intro (hsame_refl realSeal) realSealClosed)
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
          And.intro (hsame_trans (hsame_symm sameRows) sourceRow.left)
            (unary_transport sourceRow.right sameRows)
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow.left provenancePkg
  }

end BEDC.Derived.ContinuityCarrierNameCertUp
