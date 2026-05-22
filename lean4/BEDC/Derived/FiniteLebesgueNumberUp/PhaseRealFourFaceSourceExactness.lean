import BEDC.Derived.FiniteLebesgueNumberUp.Core
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberTerminalRadiusPhaseConsumerNonescape [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow terminalRead compactRead
      compactNetRead continuousRead uniformRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont route nameRow terminalRead ->
        Cont terminalRead radius compactRead ->
          Cont compactRead mesh compactNetRead ->
            Cont compactNetRead route continuousRead ->
              Cont continuousRead nameRow uniformRead ->
                PkgSig bundle uniformRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row terminalRead ∨ hsame row compactRead ∨
                          hsame row compactNetRead ∨ hsame row continuousRead ∨
                            hsame row uniformRead)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
                          hsame row uniformRead)
                      hsame ∧
                    UnaryHistory terminalRead ∧ UnaryHistory compactRead ∧
                      UnaryHistory compactNetRead ∧ UnaryHistory continuousRead ∧
                        UnaryHistory uniformRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle uniformRead pkg ∧
                            (Cont uniformRead (BHist.e0 hostTail) continuousRead ->
                              False) ∧
                              (Cont uniformRead (BHist.e1 hostTail) continuousRead ->
                                False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier routeNameTerminal terminalRadiusCompact compactMeshNet netRouteContinuous
    continuousNameUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameTerminal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed terminalUnary radiusUnary terminalRadiusCompact
  have compactNetUnary : UnaryHistory compactNetRead :=
    unary_cont_closed compactUnary meshUnary compactMeshNet
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactNetUnary routeUnary netRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminalRead ∨ hsame row compactRead ∨
              hsame row compactNetRead ∨ hsame row continuousRead ∨
                hsame row uniformRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
              hsame row uniformRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformRead sourceUniform
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, uniformPkg, source.left⟩
  }
  exact
    ⟨cert, terminalUnary, compactUnary, compactNetUnary, continuousUnary,
      uniformUnary, provenancePkg, uniformPkg,
      fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left continuousNameUniform hostReturn,
      fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right continuousNameUniform hostReturn⟩

end BEDC.Derived.FiniteLebesgueNumberUp
