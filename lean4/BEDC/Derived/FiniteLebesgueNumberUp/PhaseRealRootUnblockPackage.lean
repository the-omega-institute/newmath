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

theorem FiniteLebesgueNumberPhaseRealRootUnblockPackage [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow classifierRead compactRead
      terminalRead l10Read uniformRead hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover radius classifierRead →
        Cont classifierRead mesh compactRead →
          Cont route nameRow terminalRead →
            Cont terminalRead radius l10Read →
              Cont l10Read nameRow uniformRead →
                PkgSig bundle uniformRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row classifierRead ∨ hsame row terminalRead ∨
                          hsame row uniformRead)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle uniformRead pkg ∧
                          hsame row uniformRead)
                      hsame ∧
                    UnaryHistory classifierRead ∧ UnaryHistory compactRead ∧
                      UnaryHistory terminalRead ∧ UnaryHistory l10Read ∧
                        UnaryHistory uniformRead ∧ Cont cover radius classifierRead ∧
                          Cont classifierRead mesh compactRead ∧
                            Cont route nameRow terminalRead ∧
                              Cont terminalRead radius l10Read ∧
                                Cont l10Read nameRow uniformRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle uniformRead pkg ∧
                                      (Cont uniformRead (BHist.e0 hostTail) l10Read →
                                        False) ∧
                                        (Cont uniformRead (BHist.e1 hostTail) l10Read →
                                          False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier coverRadiusClassifier classifierMeshCompact routeNameTerminal
    terminalRadiusL10 l10NameUniform uniformPkg
  obtain ⟨coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed coverUnary radiusUnary coverRadiusClassifier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed classifierUnary meshUnary classifierMeshCompact
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed routeUnary nameRowUnary routeNameTerminal
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed terminalUnary radiusUnary terminalRadiusL10
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed l10Unary nameRowUnary l10NameUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row classifierRead ∨ hsame row terminalRead ∨ hsame row uniformRead)
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, uniformPkg, source.left⟩
  }
  exact
    ⟨cert, classifierUnary, compactUnary, terminalUnary, l10Unary, uniformUnary,
      coverRadiusClassifier, classifierMeshCompact, routeNameTerminal, terminalRadiusL10,
      l10NameUniform, provenancePkg, uniformPkg,
      fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.left l10NameUniform hostReturn,
      fun hostReturn =>
        cont_mutual_extension_right_tail_absurd.right l10NameUniform hostReturn⟩

end BEDC.Derived.FiniteLebesgueNumberUp
