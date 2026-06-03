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

theorem LocallyCompactCompletionConsumerRoute [AskSetup] [PackageSetup]
    {X x r B K A H C P N compactRead locatedRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont B K compactRead ->
      Cont compactRead A locatedRead ->
        Cont locatedRead H completionRead ->
          PkgSig bundle P pkg ->
            PkgSig bundle N pkg ->
              UnaryHistory B ->
                UnaryHistory K ->
                  UnaryHistory A ->
                    UnaryHistory H ->
                      SemanticNameCert
                          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row X ∨ hsame row x ∨ hsame row r ∨ hsame row B ∨
                              hsame row K ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨
                                hsame row P ∨ hsame row N ∨ Cont B K compactRead ∨
                                  Cont compactRead A locatedRead ∨
                                    Cont locatedRead H completionRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory compactRead ∧ UnaryHistory locatedRead ∧
                          UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro compactRoute locatedRoute completionRoute provenancePkg localNamePkg
    closedBallUnary compactWitnessUnary locatedHandoffUnary consumerUnary
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed closedBallUnary compactWitnessUnary compactRoute
  have locatedReadUnary : UnaryHistory locatedRead :=
    unary_cont_closed compactReadUnary locatedHandoffUnary locatedRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed locatedReadUnary consumerUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row x ∨ hsame row r ∨ hsame row B ∨ hsame row K ∨
              hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                Cont B K compactRead ∨ Cont compactRead A locatedRead ∨
                  Cont locatedRead H completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      intro _row _source
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr completionRoute)))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, compactReadUnary, locatedReadUnary, completionReadUnary⟩

theorem LocallyCompactCompactNeighbourhoodBasis [AskSetup] [PackageSetup]
    {metricSource point radius closedBall compactWitness locatedHandoff transport consumer
      provenance localName basisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metricSource ->
      UnaryHistory point ->
        UnaryHistory radius ->
          UnaryHistory locatedHandoff ->
            UnaryHistory provenance ->
              UnaryHistory localName ->
                Cont metricSource point closedBall ->
                  Cont closedBall radius compactWitness ->
                    Cont compactWitness locatedHandoff transport ->
                      Cont transport provenance consumer ->
                        Cont consumer localName basisRead ->
                          PkgSig bundle provenance pkg ->
                            PkgSig bundle localName pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row metricSource ∨ hsame row radius ∨
                                      hsame row closedBall ∨ hsame row compactWitness ∨
                                        hsame row basisRead)
                                  (fun _row : BHist =>
                                    PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                                  hsame ∧
                                UnaryHistory closedBall ∧ UnaryHistory compactWitness ∧
                                  UnaryHistory transport ∧ UnaryHistory consumer ∧
                                    UnaryHistory basisRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro metricUnary pointUnary radiusUnary locatedUnary provenanceUnary localNameUnary
    closedBallRoute compactRoute transportRoute consumerRoute basisRoute provenancePkg localNamePkg
  have closedBallUnary : UnaryHistory closedBall :=
    unary_cont_closed metricUnary pointUnary closedBallRoute
  have compactUnary : UnaryHistory compactWitness :=
    unary_cont_closed closedBallUnary radiusUnary compactRoute
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed compactUnary locatedUnary transportRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed transportUnary provenanceUnary consumerRoute
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed consumerUnary localNameUnary basisRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row basisRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metricSource ∨ hsame row radius ∨ hsame row closedBall ∨
              hsame row compactWitness ∨ hsame row basisRead)
          (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro basisRead ⟨hsame_refl basisRead, basisUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, closedBallUnary, compactUnary, transportUnary, consumerUnary, basisUnary⟩

end BEDC.Derived.LocallyCompactUp
