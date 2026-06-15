import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.BoundedResidualSubstitutionFrontierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedResidualSubstitutionFrontierNamecertObligations [AskSetup] [PackageSetup]
    {redex residual checker join obstruction transport replay provenance localName
      redexResidual checkerJoin frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory redex →
      UnaryHistory residual →
        UnaryHistory checker →
          UnaryHistory join →
            UnaryHistory obstruction →
              UnaryHistory transport →
                UnaryHistory replay →
                  Cont redex residual redexResidual →
                    Cont checker join checkerJoin →
                      Cont redexResidual checkerJoin frontierRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                              (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row redex ∨ hsame row residual ∨ hsame row checker ∨
                                  hsame row join ∨ hsame row obstruction ∨
                                    hsame row frontierRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle localName pkg ∧
                                    Cont redexResidual checkerJoin frontierRead)
                              hsame ∧
                              UnaryHistory redexResidual ∧ UnaryHistory checkerJoin ∧
                                UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro redexUnary residualUnary checkerUnary joinUnary _obstructionUnary _transportUnary
    _replayUnary redexResidualRoute checkerJoinRoute frontierRoute provenancePkg localNamePkg
  have redexResidualUnary : UnaryHistory redexResidual :=
    unary_cont_closed redexUnary residualUnary redexResidualRoute
  have checkerJoinUnary : UnaryHistory checkerJoin :=
    unary_cont_closed checkerUnary joinUnary checkerJoinRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed redexResidualUnary checkerJoinUnary frontierRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row redex ∨ hsame row residual ∨ hsame row checker ∨
            hsame row join ∨ hsame row obstruction ∨ hsame row frontierRead)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
            Cont redexResidual checkerJoin frontierRead)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
        constructor
        · exact hsame_trans (hsame_symm sameRows) source.left
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg, frontierRoute⟩
  }
  exact ⟨cert, redexResidualUnary, checkerJoinUnary, frontierUnary⟩

end BEDC.Derived.BoundedResidualSubstitutionFrontierUp
