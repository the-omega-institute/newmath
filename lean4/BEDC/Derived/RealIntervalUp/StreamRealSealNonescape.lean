import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalStreamRealSealNonescape [AskSetup] [PackageSetup]
    {L U E D W R S H C P N streamWindowRead streamSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L → UnaryHistory U → UnaryHistory E → UnaryHistory D → UnaryHistory W →
      UnaryHistory H → UnaryHistory N → Cont D W R → Cont W R streamWindowRead →
        Cont E streamWindowRead S → Cont S H C → Cont C N streamSealRead →
          PkgSig bundle P pkg → PkgSig bundle N pkg →
            SemanticNameCert
                (fun row : BHist => hsame row streamSealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨
                    hsame row W ∨ hsame row R ∨ hsame row streamWindowRead ∨
                      hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row streamSealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont D W R ∧ Cont W R streamWindowRead ∧
                    Cont E streamWindowRead S ∧ Cont S H C ∧ Cont C N streamSealRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                hsame ∧
              UnaryHistory R ∧ UnaryHistory streamWindowRead ∧ UnaryHistory S ∧
                UnaryHistory C ∧ UnaryHistory streamSealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro _lUnary _uUnary eUnary dUnary wUnary hUnary nUnary windowRoute streamRoute
    sealRoute consumerRoute streamSealRoute provenancePkg namePkg
  have readbackUnary : UnaryHistory R :=
    unary_cont_closed dUnary wUnary windowRoute
  have streamWindowUnary : UnaryHistory streamWindowRead :=
    unary_cont_closed wUnary readbackUnary streamRoute
  have sealUnary : UnaryHistory S :=
    unary_cont_closed eUnary streamWindowUnary sealRoute
  have consumerUnary : UnaryHistory C :=
    unary_cont_closed sealUnary hUnary consumerRoute
  have streamSealUnary : UnaryHistory streamSealRead :=
    unary_cont_closed consumerUnary nUnary streamSealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row streamSealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨
              hsame row W ∨ hsame row R ∨ hsame row streamWindowRead ∨
                hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row streamSealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W R ∧ Cont W R streamWindowRead ∧
              Cont E streamWindowRead S ∧ Cont S H C ∧ Cont C N streamSealRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro streamSealRead ⟨hsame_refl streamSealRead, streamSealUnary⟩
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
      repeat right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, streamRoute, sealRoute, consumerRoute,
          streamSealRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, readbackUnary, streamWindowUnary, sealUnary, consumerUnary, streamSealUnary⟩

end BEDC.Derived.RealIntervalUp
