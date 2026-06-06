import BEDC.Derived.DyadicIntervalArithmeticUp.EnclosureSoundness
import BEDC.Derived.DyadicIntervalArithmeticUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicIntervalArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalArithmeticCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {lower upper order addDelta mulDelta refinement enclosure transport replay provenance
      localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory lower →
      UnaryHistory upper →
        UnaryHistory addDelta →
          UnaryHistory refinement →
            UnaryHistory replay →
              Cont lower upper order →
                Cont order addDelta enclosure →
                  Cont enclosure replay refinement →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle localCert pkg →
                        SemanticNameCert
                          (fun row : BHist => hsame row enclosure ∨ hsame row refinement)
                          (fun row : BHist => UnaryHistory row)
                          (fun _row : BHist =>
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg)
                          hsame ∧
                          UnaryHistory order ∧ UnaryHistory enclosure ∧
                            UnaryHistory refinement ∧ Cont lower upper order ∧
                              Cont order addDelta enclosure ∧
                                Cont enclosure replay refinement := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro lowerUnary upperUnary addDeltaUnary refinementUnary replayUnary orderCont
    enclosureCont refinementCont provenancePkg localCertPkg
  have mulDeltaRow : BHist := mulDelta
  have transportRow : BHist := transport
  have orderUnary : UnaryHistory order :=
    unary_cont_closed lowerUnary upperUnary orderCont
  have enclosureUnary : UnaryHistory enclosure :=
    unary_cont_closed orderUnary addDeltaUnary enclosureCont
  have refinementUnaryFromRoute : UnaryHistory refinement :=
    unary_cont_closed enclosureUnary replayUnary refinementCont
  have enclosureSource :
      (fun row : BHist => hsame row enclosure ∨ hsame row refinement) enclosure := by
    exact Or.inl (hsame_refl enclosure)
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row enclosure ∨ hsame row refinement)
        (fun row : BHist => UnaryHistory row)
        (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle localCert pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro enclosure enclosureSource
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
        cases source with
        | inl sameEnclosure =>
            exact Or.inl (hsame_trans (hsame_symm same) sameEnclosure)
        | inr sameRefinement =>
            exact Or.inr (hsame_trans (hsame_symm same) sameRefinement)
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameEnclosure =>
          exact unary_transport enclosureUnary (hsame_symm sameEnclosure)
      | inr sameRefinement =>
          exact unary_transport refinementUnary (hsame_symm sameRefinement)
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, localCertPkg⟩
  }
  exact
    ⟨cert, orderUnary, enclosureUnary, refinementUnaryFromRoute, orderCont, enclosureCont,
      refinementCont⟩

theorem DyadicIntervalArithmeticCarrier_enclosure_namecert_handoff [AskSetup] [PackageSetup]
    {lower upper order addDelta mulDelta refinement enclosure transport replay provenance
      localCert operationRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalArithmeticCarrier lower upper order addDelta mulDelta refinement enclosure
      transport replay provenance localCert bundle pkg →
      Cont order addDelta operationRead →
        Cont operationRead enclosure handoffRead →
          PkgSig bundle handoffRead pkg →
            SemanticNameCert
              (fun row : BHist => hsame row handoffRead)
              (fun row : BHist => UnaryHistory row)
              (fun row : BHist => PkgSig bundle row pkg)
              hsame ∧
              UnaryHistory operationRead ∧ UnaryHistory handoffRead ∧
                Cont order addDelta operationRead ∧
                  Cont operationRead enclosure handoffRead ∧ PkgSig bundle handoffRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier operationCont handoffCont handoffPkg
  have sound :=
    DyadicIntervalArithmeticCarrier_enclosure_soundness carrier operationCont handoffCont
      handoffPkg
  obtain
    ⟨_lowerUnary, _upperUnary, _orderUnary, operationUnary, handoffUnary, operationContOut,
      handoffContOut, handoffPkgOut⟩ := sound
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row handoffRead)
        (fun row : BHist => UnaryHistory row)
        (fun row : BHist => PkgSig bundle row pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead (hsame_refl handoffRead)
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
        exact hsame_trans (hsame_symm same) source
    }
    pattern_sound := by
      intro row sameHandoff
      exact unary_transport handoffUnary (hsame_symm sameHandoff)
    ledger_sound := by
      intro row sameHandoff
      cases sameHandoff
      exact handoffPkgOut
  }
  exact
    ⟨cert, operationUnary, handoffUnary, operationContOut, handoffContOut, handoffPkgOut⟩

end BEDC.Derived.DyadicIntervalArithmeticUp
