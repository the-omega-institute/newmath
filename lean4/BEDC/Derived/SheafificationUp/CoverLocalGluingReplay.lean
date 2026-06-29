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

theorem SheafificationCoverLocalGluingReplay [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverRead localityRead gluingRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T coverRead →
        Cont coverRead L localityRead →
          Cont localityRead G gluingRead →
            Cont gluingRead R replayRead →
              PkgSig bundle replayRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                        hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                          hsame row R ∨ hsame row Q ∨ hsame row N ∨
                            hsame row coverRead ∨ hsame row localityRead ∨
                              hsame row gluingRead ∨ hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont C T coverRead ∧
                        Cont coverRead L localityRead ∧
                          Cont localityRead G gluingRead ∧
                            Cont gluingRead R replayRead ∧ PkgSig bundle replayRead pkg)
                    hsame ∧ UnaryHistory coverRead ∧ UnaryHistory localityRead ∧
                  UnaryHistory gluingRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: SheafificationCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverRoute localityRoute gluingRoute replayRoute replayPkg
  obtain ⟨cUnary, tUnary, _jUnary, _pUnary, lUnary, gUnary, _sUnary, _hUnary,
    rUnary, _qUnary, _nUnary, _qPkgCarrier, _nPkgCarrier⟩ := carrier
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed cUnary tUnary coverRoute
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed coverUnary lUnary localityRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityUnary gUnary gluingRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed gluingUnary rUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨ hsame row L ∨
              hsame row G ∨ hsame row S ∨ hsame row H ∨ hsame row R ∨ hsame row Q ∨
                hsame row N ∨ hsame row coverRead ∨ hsame row localityRead ∨
                  hsame row gluingRead ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C T coverRead ∧ Cont coverRead L localityRead ∧
              Cont localityRead G gluingRead ∧ Cont gluingRead R replayRead ∧
                PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, coverRoute, localityRoute, gluingRoute, replayRoute, replayPkg⟩
  }
  exact ⟨cert, coverUnary, localityUnary, gluingUnary, replayUnary⟩

end BEDC.Derived.SheafificationUp
