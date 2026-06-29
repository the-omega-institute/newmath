import BEDC.Derived.SheafificationUp.TasteGate
import BEDC.FKernel.Cont

namespace BEDC.Derived.SheafificationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SheafificationPresheafSheafRoute [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N localRead gluingRead transportedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont P L localRead →
        Cont localRead G gluingRead →
          hsame transportedRead gluingRead →
            Cont transportedRead R replayRead →
              PkgSig bundle Q pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row S ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row P ∨ hsame row L ∨ hsame row G ∨ hsame row S ∨
                          hsame row H ∨ hsame row R ∨ hsame row Q ∨ hsame row N ∨
                            hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont P L localRead ∧
                          Cont localRead G gluingRead ∧
                            Cont transportedRead R replayRead ∧
                              PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
                      hsame ∧
                    UnaryHistory localRead ∧ UnaryHistory gluingRead ∧
                      UnaryHistory transportedRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier localRoute gluingRoute transportedSame replayRoute qPkg nPkg
  obtain ⟨_cUnary, _tUnary, _jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary,
    rUnary, _qUnary, _nUnary, _carrierQPkg, _carrierNPkg⟩ := carrier
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed pUnary lUnary localRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localUnary gUnary gluingRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_transport gluingUnary (hsame_symm transportedSame)
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed transportedUnary rUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row S ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row P ∨ hsame row L ∨ hsame row G ∨ hsame row S ∨
              hsame row H ∨ hsame row R ∨ hsame row Q ∨ hsame row N ∨
                hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont P L localRead ∧ Cont localRead G gluingRead ∧
              Cont transportedRead R replayRead ∧ PkgSig bundle Q pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro S ⟨hsame_refl S, sUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localRoute, gluingRoute, replayRoute, qPkg, nPkg⟩
  }
  exact ⟨cert, localUnary, gluingUnary, transportedUnary, replayUnary⟩

end BEDC.Derived.SheafificationUp
