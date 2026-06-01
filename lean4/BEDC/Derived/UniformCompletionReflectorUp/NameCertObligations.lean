import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformCompletionReflectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniformCompletionReflectorCarrier [AskSetup] [PackageSetup]
    (X W Y J Q H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig hsame
  UnaryHistory X ∧ UnaryHistory W ∧ UnaryHistory Y ∧ UnaryHistory J ∧
    UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont X W Y ∧ Cont Y J Q ∧ hsame H C ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem UniformCompletionReflectorNameCertObligations [AskSetup] [PackageSetup]
    {X W Y J Q H C P N replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCompletionReflectorCarrier X W Y J Q H C P N bundle pkg ->
      Cont X W Y ->
        Cont Y J Q ->
          Cont Q H replayRead ->
            PkgSig bundle replayRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row W ∨ hsame row Y ∨ hsame row J ∨
                      hsame row Q ∨ hsame row replayRead)
                  (fun row : BHist =>
                    hsame row replayRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle replayRead pkg)
                  hsame ∧
                UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont UnaryHistory
  intro carrier sourceWindow targetDense universalReplay replayPkg
  obtain ⟨sourceUnary, windowUnary, _targetUnary, denseUnary, _universalUnary, transportUnary,
    _replayUnary, _provenanceUnary, _localUnary, _carrierSourceWindow, _carrierTargetDense,
    _transportReplay, provenancePkg, _localPkg⟩ := carrier
  have targetReadUnary : UnaryHistory Y :=
    unary_cont_closed sourceUnary windowUnary sourceWindow
  have universalReadUnary : UnaryHistory Q :=
    unary_cont_closed targetReadUnary denseUnary targetDense
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed universalReadUnary transportUnary universalReplay
  have sourceWitness :
      hsame replayRead replayRead ∧ UnaryHistory replayRead :=
    ⟨hsame_refl replayRead, replayReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row W ∨ hsame row Y ∨ hsame row J ∨ hsame row Q ∨
              hsame row replayRead)
          (fun row : BHist =>
            hsame row replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle replayRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro replayRead sourceWitness
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
        intro row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.left, provenancePkg, replayPkg⟩
    }
  exact ⟨cert, replayReadUnary⟩

end BEDC.Derived.UniformCompletionReflectorUp
