import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalPublicNameCertExport [AskSetup] [PackageSetup]
    {L U E D W R S H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L → UnaryHistory U → UnaryHistory E → UnaryHistory D → UnaryHistory W →
      UnaryHistory H → UnaryHistory N → Cont L U E → Cont D W R → Cont E R S →
        Cont S H C → Cont C N publicRead → PkgSig bundle P pkg → PkgSig bundle N pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨
                  hsame row W ∨ hsame row R ∨ hsame row S ∨ hsame row H ∨
                    hsame row C ∨ hsame row N ∨ hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont L U E ∧ Cont D W R ∧ Cont E R S ∧
                  Cont S H C ∧ Cont C N publicRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro _lUnary _uUnary eUnary dUnary wUnary hUnary nUnary _endpointRoute windowRoute
    sealRoute consumerRoute publicRoute provenancePkg namePkg
  have readbackUnary : UnaryHistory R :=
    unary_cont_closed dUnary wUnary windowRoute
  have sealUnary : UnaryHistory S :=
    unary_cont_closed eUnary readbackUnary sealRoute
  have consumerUnary : UnaryHistory C :=
    unary_cont_closed sealUnary hUnary consumerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed consumerUnary nUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨ hsame row W ∨
              hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row N ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U E ∧ Cont D W R ∧ Cont E R S ∧ Cont S H C ∧
              Cont C N publicRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, _endpointRoute, windowRoute, sealRoute, consumerRoute, publicRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.RealIntervalUp
