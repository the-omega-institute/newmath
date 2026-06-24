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

theorem SheafificationSourceObligationPackage [AskSetup] [PackageSetup]
    {C T J P L G S H R Q N coverWindow restrictionRead localityRead sheafRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SheafificationCarrier C T J P L G S H R Q N bundle pkg →
      Cont C T coverWindow →
        Cont J P restrictionRead →
          Cont coverWindow restrictionRead localityRead →
            Cont localityRead S sheafRead →
              PkgSig bundle sheafRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
                        hsame row L ∨ hsame row G ∨ hsame row S ∨
                          hsame row localityRead ∨ hsame row sheafRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont C T coverWindow ∧
                        Cont J P restrictionRead ∧
                          Cont coverWindow restrictionRead localityRead ∧
                            Cont localityRead S sheafRead ∧
                              PkgSig bundle sheafRead pkg)
                    hsame ∧
                  UnaryHistory coverWindow ∧ UnaryHistory restrictionRead ∧
                    UnaryHistory localityRead ∧ UnaryHistory sheafRead ∧
                      PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier coverRoute restrictionRoute localityRoute sheafRoute sheafPkg
  obtain ⟨cUnary, tUnary, jUnary, pUnary, _lUnary, _gUnary, sUnary, _hUnary,
    _rUnary, _qUnary, _nUnary, namePkg⟩ := carrier
  have coverWindowUnary : UnaryHistory coverWindow :=
    unary_cont_closed cUnary tUnary coverRoute
  have restrictionReadUnary : UnaryHistory restrictionRead :=
    unary_cont_closed jUnary pUnary restrictionRoute
  have localityReadUnary : UnaryHistory localityRead :=
    unary_cont_closed coverWindowUnary restrictionReadUnary localityRoute
  have sheafReadUnary : UnaryHistory sheafRead :=
    unary_cont_closed localityReadUnary sUnary sheafRoute
  have sourceSheaf :
      (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row) sheafRead :=
    ⟨hsame_refl sheafRead, sheafReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sheafRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row T ∨ hsame row J ∨ hsame row P ∨
              hsame row L ∨ hsame row G ∨ hsame row S ∨
                hsame row localityRead ∨ hsame row sheafRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C T coverWindow ∧ Cont J P restrictionRead ∧
              Cont coverWindow restrictionRead localityRead ∧
                Cont localityRead S sheafRead ∧ PkgSig bundle sheafRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sheafRead sourceSheaf
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
        ⟨source.right, coverRoute, restrictionRoute, localityRoute, sheafRoute, sheafPkg⟩
  }
  exact
    ⟨cert, coverWindowUnary, restrictionReadUnary, localityReadUnary, sheafReadUnary,
      namePkg⟩

end BEDC.Derived.SheafificationUp
