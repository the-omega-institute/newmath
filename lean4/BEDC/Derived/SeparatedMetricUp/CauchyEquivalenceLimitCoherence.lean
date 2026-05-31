import BEDC.Derived.SeparatedMetricUp.TasteGate

namespace BEDC.Derived.SeparatedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedMetricCauchyEquivalenceLimitCoherence [AskSetup] [PackageSetup]
    {metricRow zeroSeal separatedRow limitLeft limitRight equivalenceRow transport replay
      provenance localName coherenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metricRow →
      UnaryHistory zeroSeal →
        UnaryHistory separatedRow →
          UnaryHistory limitLeft →
            UnaryHistory limitRight →
              UnaryHistory equivalenceRow →
                UnaryHistory transport →
                  UnaryHistory replay →
                    UnaryHistory provenance →
                      UnaryHistory localName →
                        Cont limitLeft limitRight equivalenceRow →
                          Cont equivalenceRow metricRow zeroSeal →
                            Cont zeroSeal separatedRow coherenceRead →
                              PkgSig bundle provenance pkg →
                                PkgSig bundle localName pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row coherenceRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row limitLeft ∨ hsame row limitRight ∨
                                          hsame row equivalenceRow ∨ hsame row metricRow ∨
                                            hsame row zeroSeal ∨ hsame row separatedRow ∨
                                              hsame row coherenceRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                          PkgSig bundle localName pkg ∧
                                            Cont zeroSeal separatedRow coherenceRead)
                                      hsame ∧
                                    UnaryHistory coherenceRead ∧
                                      PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro metricUnary _zeroUnary separatedUnary limitLeftUnary limitRightUnary
    _equivalenceUnary _transportUnary _replayUnary _provenanceUnary _localNameUnary
    limitEquivalenceRoute equivalenceZeroRoute zeroSeparatedCoherence provenancePkg localNamePkg
  have equivalenceFromLimits : UnaryHistory equivalenceRow :=
    unary_cont_closed limitLeftUnary limitRightUnary limitEquivalenceRoute
  have zeroFromEquivalence : UnaryHistory zeroSeal :=
    unary_cont_closed equivalenceFromLimits metricUnary equivalenceZeroRoute
  have coherenceUnary : UnaryHistory coherenceRead :=
    unary_cont_closed zeroFromEquivalence separatedUnary zeroSeparatedCoherence
  have sourceCoherence :
      (fun row : BHist => hsame row coherenceRead ∧ UnaryHistory row) coherenceRead := by
    exact ⟨hsame_refl coherenceRead, coherenceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coherenceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row limitLeft ∨ hsame row limitRight ∨ hsame row equivalenceRow ∨
              hsame row metricRow ∨ hsame row zeroSeal ∨ hsame row separatedRow ∨
                hsame row coherenceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg ∧ Cont zeroSeal separatedRow coherenceRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro coherenceRead sourceCoherence
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
      exact ⟨source.right, provenancePkg, localNamePkg, zeroSeparatedCoherence⟩
  }
  exact ⟨cert, coherenceUnary, provenancePkg⟩

end BEDC.Derived.SeparatedMetricUp
