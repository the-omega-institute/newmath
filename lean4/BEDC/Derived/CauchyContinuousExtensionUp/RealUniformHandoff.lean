import BEDC.Derived.CauchyContinuousExtensionUp.UniformModulusSink
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyContinuousExtensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyContinuousExtensionCarrier_real_uniform_handoff [AskSetup] [PackageSetup]
    {S W D F U L H C P N sourceRead toleranceRead mapRead extensionRead replayRead
      realUniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyExtensionUniformModulusSink S W D F U L H C P N sourceRead toleranceRead mapRead
        extensionRead replayRead bundle pkg ->
      Cont replayRead U realUniformRead ->
        PkgSig bundle realUniformRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row realUniformRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row W ∨ hsame row D ∨ hsame row F ∨ hsame row U ∨
                  hsame row realUniformRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont replayRead U realUniformRead ∧
                  PkgSig bundle realUniformRead pkg)
              hsame ∧
            UnaryHistory realUniformRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro sink realUniformRoute realUniformPkg
  obtain ⟨_fields, sourceUnary, windowUnary, dyadicUnary, mapUnary, extensionUnary,
    replayConsumerUnary, sourceRoute, toleranceRoute, mapRoute, extensionRoute, replayRoute,
    provenancePkg, localCertPkg⟩ := sink
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary windowUnary sourceRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed sourceReadUnary dyadicUnary toleranceRoute
  have mapReadUnary : UnaryHistory mapRead :=
    unary_cont_closed toleranceReadUnary mapUnary mapRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed mapReadUnary extensionUnary extensionRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed extensionReadUnary replayConsumerUnary replayRoute
  have realUniformUnary : UnaryHistory realUniformRead :=
    unary_cont_closed replayUnary extensionUnary realUniformRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realUniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row D ∨ hsame row F ∨ hsame row U ∨
              hsame row realUniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont replayRead U realUniformRead ∧
              PkgSig bundle realUniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realUniformRead
          ⟨hsame_refl realUniformRead, realUniformUnary⟩
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
          intro row other sameRows source
          have otherSame : hsame other realUniformRead :=
            hsame_trans (hsame_symm sameRows) source.left
          have otherUnary : UnaryHistory other :=
            unary_transport source.right sameRows
          exact ⟨otherSame, otherUnary⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, realUniformRoute, realUniformPkg⟩
    }
  exact ⟨cert, realUniformUnary, provenancePkg, localCertPkg⟩

end BEDC.Derived.CauchyContinuousExtensionUp
