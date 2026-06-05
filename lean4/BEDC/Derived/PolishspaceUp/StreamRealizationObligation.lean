import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceStreamRealizationObligation [AskSetup] [PackageSetup]
    {M K D S R W H C G N denseRead scheduleRead streamRead readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg →
      Cont M D denseRead →
        Cont denseRead S scheduleRead →
          Cont scheduleRead R streamRead →
            Cont streamRead W readbackRead →
              PkgSig bundle G pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row M ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨
                          hsame row W ∨ hsame row denseRead ∨ hsame row scheduleRead ∨
                            hsame row streamRead ∨ hsame row readbackRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M D denseRead ∧
                          Cont denseRead S scheduleRead ∧
                            Cont scheduleRead R streamRead ∧
                              Cont streamRead W readbackRead ∧ PkgSig bundle G pkg ∧
                                PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory denseRead ∧ UnaryHistory scheduleRead ∧
                      UnaryHistory streamRead ∧ UnaryHistory readbackRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute scheduleRoute streamRoute readbackRoute gPkg nPkg
  obtain ⟨mUnary, _kUnary, dUnary, sUnary, rUnary, wUnary, _hUnary, _cUnary,
    _gUnary, _nUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, _carrierGPkg, _carrierNPkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed mUnary dUnary denseRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed denseUnary sUnary scheduleRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed scheduleUnary rUnary streamRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed streamUnary wUnary readbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readbackRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row D ∨ hsame row S ∨ hsame row R ∨ hsame row W ∨
              hsame row denseRead ∨ hsame row scheduleRead ∨ hsame row streamRead ∨
                hsame row readbackRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M D denseRead ∧ Cont denseRead S scheduleRead ∧
              Cont scheduleRead R streamRead ∧ Cont streamRead W readbackRead ∧
                PkgSig bundle G pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro readbackRead ⟨hsame_refl readbackRead, readbackUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, scheduleRoute, streamRoute, readbackRoute, gPkg, nPkg⟩
  }
  exact ⟨cert, denseUnary, scheduleUnary, streamUnary, readbackUnary⟩

end BEDC.Derived.PolishspaceUp
