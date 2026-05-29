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

theorem LocallyCompactClosedBallNeighborhoodBase [AskSetup] [PackageSetup]
    {metricSource point radius closedBall compactWitness locatedHandoff transport consumer
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metricSource →
      UnaryHistory point →
        UnaryHistory radius →
          UnaryHistory locatedHandoff →
            UnaryHistory provenance →
              Cont metricSource point closedBall →
                Cont closedBall radius compactWitness →
                  Cont compactWitness locatedHandoff transport →
                    Cont transport provenance consumer →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle localName pkg →
                          SemanticNameCert
                            (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row metricSource ∨ hsame row closedBall ∨
                                hsame row compactWitness ∨ hsame row consumer)
                            (fun _row : BHist =>
                              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                            hsame ∧
                            UnaryHistory closedBall ∧
                              UnaryHistory compactWitness ∧
                                UnaryHistory transport ∧
                                  UnaryHistory consumer ∧
                                    Cont metricSource point closedBall ∧
                                      Cont closedBall radius compactWitness ∧
                                        Cont compactWitness locatedHandoff transport ∧
                                          Cont transport provenance consumer := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro metricUnary pointUnary radiusUnary locatedUnary provenanceUnary closedBallRoute
    compactRoute transportRoute consumerRoute provenancePkg localNamePkg
  have closedBallUnary : UnaryHistory closedBall :=
    unary_cont_closed metricUnary pointUnary closedBallRoute
  have compactUnary : UnaryHistory compactWitness :=
    unary_cont_closed closedBallUnary radiusUnary compactRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed compactUnary locatedUnary transportRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed transportUnary provenanceUnary consumerRoute
  have consumerSource :
      (fun row : BHist => hsame row consumer ∧ UnaryHistory row) consumer := by
    exact ⟨hsame_refl consumer, consumerUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row consumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row metricSource ∨ hsame row closedBall ∨ hsame row compactWitness ∨
            hsame row consumer)
        (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro consumer consumerSource
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
        intro row other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.1,
            unary_transport source.2 same⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr source.1))
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, closedBallUnary, compactUnary, transportUnary, consumerUnary, closedBallRoute,
      compactRoute, transportRoute, consumerRoute⟩

end BEDC.Derived.LocallyCompactUp
