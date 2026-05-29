import BEDC.Derived.NormedSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def NormedSpaceCarrier [AskSetup] [PackageSetup]
    (V R N M Q H T P C : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory V ∧ UnaryHistory R ∧ UnaryHistory N ∧ UnaryHistory M ∧
    UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory T ∧ UnaryHistory P ∧
      UnaryHistory C ∧ Cont V R N ∧ Cont N M Q ∧ Cont Q H T ∧
        PkgSig bundle P pkg ∧ PkgSig bundle C pkg

theorem NormedSpaceCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {V R N M Q H T P C metricRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V N metricRead ->
        Cont M Q completionRead ->
          PkgSig bundle completionRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
                    hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                      hsame row C ∨ hsame row metricRead ∨ hsame row completionRead)
                (fun row : BHist =>
                  hsame row completionRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle completionRead pkg)
                hsame ∧
              UnaryHistory metricRead ∧ UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier metricRoute completionRoute completionPkg
  obtain ⟨VUnary, _RUnary, NUnary, MUnary, QUnary, _HUnary, _TUnary, _PUnary, _CUnary,
    _vectorNormRoute, _completionFacingRoute, _replayRoute, provenancePkg, _localPkg⟩ :=
      carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed VUnary NUnary metricRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary QUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row R ∨ hsame row N ∨ hsame row M ∨
              hsame row Q ∨ hsame row H ∨ hsame row T ∨ hsame row P ∨
                hsame row C ∨ hsame row metricRead ∨ hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr sourceRow.left)))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, provenancePkg, completionPkg⟩
  }
  exact ⟨cert, metricUnary, completionUnary⟩

end BEDC.Derived.NormedSpaceUp
