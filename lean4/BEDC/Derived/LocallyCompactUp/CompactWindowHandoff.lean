import BEDC.Derived.LocallyCompactUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocallyCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocallyCompactCompactWindowHandoff [AskSetup] [PackageSetup]
    {metricSource point radius closedBall compactWitness locatedHandoff compactRead handoffRead
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metricSource ->
      UnaryHistory point ->
        UnaryHistory radius ->
          UnaryHistory locatedHandoff ->
            UnaryHistory provenance ->
              Cont metricSource point closedBall ->
                Cont closedBall radius compactWitness ->
                  Cont compactWitness locatedHandoff compactRead ->
                    Cont compactRead provenance handoffRead ->
                      PkgSig bundle provenance pkg ->
                        PkgSig bundle localName pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row metricSource ∨ hsame row point ∨ hsame row radius ∨
                                  hsame row closedBall ∨ hsame row compactWitness ∨
                                    hsame row locatedHandoff ∨ hsame row compactRead ∨
                                      hsame row handoffRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧
                                  Cont compactWitness locatedHandoff compactRead ∧
                                    Cont compactRead provenance handoffRead ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg)
                              hsame ∧
                            UnaryHistory closedBall ∧ UnaryHistory compactWitness ∧
                              UnaryHistory compactRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro unaryMetric unaryPoint unaryRadius unaryLocated unaryProvenance
  intro closedBallRoute compactWitnessRoute compactReadRoute handoffReadRoute pkgProvenance pkgLocal
  have unaryClosedBall : UnaryHistory closedBall :=
    unary_cont_closed unaryMetric unaryPoint closedBallRoute
  have unaryCompactWitness : UnaryHistory compactWitness :=
    unary_cont_closed unaryClosedBall unaryRadius compactWitnessRoute
  have unaryCompactRead : UnaryHistory compactRead :=
    unary_cont_closed unaryCompactWitness unaryLocated compactReadRoute
  have unaryHandoffRead : UnaryHistory handoffRead :=
    unary_cont_closed unaryCompactRead unaryProvenance handoffReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metricSource ∨ hsame row point ∨ hsame row radius ∨
              hsame row closedBall ∨ hsame row compactWitness ∨ hsame row locatedHandoff ∨
                hsame row compactRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compactWitness locatedHandoff compactRead ∧
              Cont compactRead provenance handoffRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro handoffRead ⟨hsame_refl handoffRead, unaryHandoffRead⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, compactReadRoute, handoffReadRoute, pkgProvenance, pkgLocal⟩
  }
  exact ⟨cert, unaryClosedBall, unaryCompactWitness, unaryCompactRead, unaryHandoffRead⟩

end BEDC.Derived.LocallyCompactUp
