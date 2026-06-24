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

theorem SheafificationLocalGluingObligation [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N sourceRead localityRead gluingRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg ->
      Cont P L localityRead ->
        Cont localityRead G gluingRead ->
          Cont gluingRead S targetRead ->
            PkgSig bundle Q pkg ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row targetRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                      hsame row L ∨ hsame row G ∨ hsame row S ∨ hsame row H ∨
                        hsame row R ∨ hsame row Q ∨ hsame row N ∨
                          hsame row targetRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont P L localityRead ∧
                      Cont localityRead G gluingRead ∧ Cont gluingRead S targetRead ∧
                        PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier localityRoute gluingRoute targetRoute provenancePkg namePkg
  obtain ⟨cUnary, tUnary, jUnary, pUnary, lUnary, gUnary, sUnary, _hUnary, _rUnary,
    _qUnary, _nUnary, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have localityUnary : UnaryHistory localityRead :=
    unary_cont_closed pUnary lUnary localityRoute
  have gluingUnary : UnaryHistory gluingRead :=
    unary_cont_closed localityUnary gUnary gluingRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed gluingUnary sUnary targetRoute
  have _sourceRows : UnaryHistory C ∧ UnaryHistory T ∧ UnaryHistory J :=
    ⟨cUnary, tUnary, jUnary⟩
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro targetRead ⟨hsame_refl targetRead, targetUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr sourceRow.left))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, localityRoute, gluingRoute, targetRoute, provenancePkg,
          namePkg⟩
  }

end BEDC.Derived.SheafificationUp
