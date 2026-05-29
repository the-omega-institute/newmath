import BEDC.Derived.SeparableMetricUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SeparableMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparableMetricCarrier_obligation_frontier [AskSetup] [PackageSetup]
    {metric denseNames window tolerance regularSeal realSeal transport _replay provenance
      localName metricWindow toleranceReplay regularRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory denseNames →
        UnaryHistory window →
          UnaryHistory tolerance →
            UnaryHistory regularSeal →
              UnaryHistory realSeal →
                UnaryHistory transport →
                  Cont metric window metricWindow →
                    Cont metric tolerance toleranceReplay →
                      Cont denseNames window regularRead →
                        Cont tolerance regularSeal completionRead →
                          PkgSig bundle provenance pkg →
                            PkgSig bundle localName pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row completionRead ∧
                                    UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row metric ∨ hsame row denseNames ∨
                                      hsame row window ∨ hsame row tolerance ∨
                                        hsame row regularSeal ∨ hsame row realSeal ∨
                                          hsame row completionRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                      PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory metricWindow ∧
                                  UnaryHistory toleranceReplay ∧
                                    UnaryHistory regularRead ∧
                                      UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro metricUnary denseUnary windowUnary toleranceUnary regularSealUnary _realSealUnary
    _transportUnary metricWindowRoute toleranceReplayRoute regularReadRoute completionReadRoute
    provenancePkg localNamePkg
  have metricWindowUnary : UnaryHistory metricWindow :=
    unary_cont_closed metricUnary windowUnary metricWindowRoute
  have toleranceReplayUnary : UnaryHistory toleranceReplay :=
    unary_cont_closed metricUnary toleranceUnary toleranceReplayRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed denseUnary windowUnary regularReadRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed toleranceUnary regularSealUnary completionReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row denseNames ∨ hsame row window ∨
              hsame row tolerance ∨ hsame row regularSeal ∨ hsame row realSeal ∨
                hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionReadUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, metricWindowUnary, toleranceReplayUnary, regularReadUnary, completionReadUnary⟩

end BEDC.Derived.SeparableMetricUp
