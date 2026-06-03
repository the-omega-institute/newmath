import BEDC.Derived.LocallyCompactUp.ClosedBallNeighborhoodBase

namespace BEDC.Derived.LocallyCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocallyCompactLocalPropernessRadiusExhaustion [AskSetup] [PackageSetup]
    {metricSource point radius closedBall compactWitness locatedHandoff transport consumer
      provenance localName radiusRead : BHist}
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
                      Cont radius consumer radiusRead →
                        PkgSig bundle provenance pkg →
                          PkgSig bundle localName pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row radiusRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row point ∨ hsame row radius ∨
                                    hsame row closedBall ∨ hsame row compactWitness ∨
                                      hsame row locatedHandoff ∨ hsame row radiusRead ∨
                                        Cont radius consumer radiusRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg)
                                hsame ∧
                              UnaryHistory radiusRead ∧
                                hsame radiusRead (append radius consumer) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory append
  intro metricUnary pointUnary radiusUnary locatedUnary provenanceUnary closedBallRoute
    compactRoute transportRoute consumerRoute radiusConsumerRoute provenancePkg localNamePkg
  have closedBallUnary : UnaryHistory closedBall :=
    unary_cont_closed metricUnary pointUnary closedBallRoute
  have compactUnary : UnaryHistory compactWitness :=
    unary_cont_closed closedBallUnary radiusUnary compactRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed compactUnary locatedUnary transportRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed transportUnary provenanceUnary consumerRoute
  have radiusReadUnary : UnaryHistory radiusRead :=
    unary_cont_closed radiusUnary consumerUnary radiusConsumerRoute
  have radiusReadExact : hsame radiusRead (append radius consumer) := by
    cases radiusConsumerRoute
    exact hsame_refl _
  have radiusReadSource :
      (fun row : BHist => hsame row radiusRead ∧ UnaryHistory row) radiusRead := by
    exact ⟨hsame_refl radiusRead, radiusReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row radiusRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row point ∨ hsame row radius ∨ hsame row closedBall ∨
              hsame row compactWitness ∨ hsame row locatedHandoff ∨
                hsame row radiusRead ∨ Cont radius consumer radiusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro radiusRead radiusReadSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, radiusReadUnary, radiusReadExact⟩

end BEDC.Derived.LocallyCompactUp
